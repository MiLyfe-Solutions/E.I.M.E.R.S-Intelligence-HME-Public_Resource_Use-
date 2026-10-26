import V185TrunkScan23Chunk0355

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2105912 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_2105912 : Nat := 118140960795 + 2105912 * 2 ^ 59
def prefixEnd_2105912 : Nat := 4983230072969 + 3 ^ 40 * 2105912 * 2
def baseEnd_2105912 : Nat := 1081345072071269843315093

theorem tailTrace_2105912 : CollatzResearch.WordTrace tailWord_2105912 prefixEnd_2105912 1081345072071269843315093 := by
  unfold tailWord_2105912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38404460373323979990311995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51205947164431973320415993 38404460373323979990311995)
  ·
    refine ⟨57606690559985969985467993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38404460373323979990311995 57606690559985969985467993)
    ·
      refine ⟨43205017919989477489100995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57606690559985969985467993 43205017919989477489100995)
      ·
        refine ⟨64807526879984216233651493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43205017919989477489100995 64807526879984216233651493)
        ·
          refine ⟨12151411289997040543809655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64807526879984216233651493 12151411289997040543809655)
          ·
            refine ⟨18227116934995560815714483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12151411289997040543809655 18227116934995560815714483)
            ·
              refine ⟨27340675402493341223571725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18227116934995560815714483 27340675402493341223571725)
              ·
                refine ⟨10252753275935002958839397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27340675402493341223571725 10252753275935002958839397)
                ·
                  refine ⟨1922391239237813054782387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10252753275935002958839397 1922391239237813054782387)
                  ·
                    refine ⟨2883586858856719582173581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922391239237813054782387 2883586858856719582173581)
                    ·
                      refine ⟨1081345072071269843315093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883586858856719582173581 1081345072071269843315093)
                      ·
                        rfl

theorem cell23_2105912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_2105912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105912 prefixEnd_2105912 := by exact prefixLift 2105912
  have htrace : WordTrace (prefixWord ++ tailWord_2105912) baseStart_2105912 baseEnd_2105912 := by
    simpa [prefixWord, tailWord_2105912, baseEnd_2105912] using wordTrace_append hprefix tailTrace_2105912
  have hstable : (prefixWord ++ tailWord_2105912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105912).length < 2 ^ (prefixWord ++ tailWord_2105912).sum := by decide
  have hdescent : baseEnd_2105912 < baseStart_2105912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105913 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2105913 : Nat := 118140960795 + 2105913 * 2 ^ 59
def prefixEnd_2105913 : Nat := 4983230072969 + 3 ^ 40 * 2105913 * 2
def baseEnd_2105913 : Nat := 1081345585551924339402589

theorem tailTrace_2105913 : CollatzResearch.WordTrace tailWord_2105913 prefixEnd_2105913 1081345585551924339402589 := by
  unfold tailWord_2105913
  simp only [CollatzResearch.WordTrace]
  refine ⟨76808957219644337151410393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51205971479762891434273595 76808957219644337151410393)
  ·
    refine ⟨57606717914733252863557795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76808957219644337151410393 57606717914733252863557795)
    ·
      refine ⟨86410076872099879295336693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57606717914733252863557795 86410076872099879295336693)
      ·
        refine ⟨8100944706759363683937815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86410076872099879295336693 8100944706759363683937815)
        ·
          refine ⟨12151417060139045525906723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8100944706759363683937815 12151417060139045525906723)
          ·
            refine ⟨18227125590208568288860085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12151417060139045525906723 18227125590208568288860085)
            ·
              refine ⟨1708793024082053277080633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18227125590208568288860085 1708793024082053277080633)
              ·
                refine ⟨1281594768061539957810475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708793024082053277080633 1281594768061539957810475)
                ·
                  refine ⟨1922392152092309936715713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281594768061539957810475 1922392152092309936715713)
                  ·
                    refine ⟨1441794114069232452536785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1922392152092309936715713 1441794114069232452536785)
                    ·
                      refine ⟨1081345585551924339402589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441794114069232452536785 1081345585551924339402589)
                      ·
                        rfl

theorem cell23_2105913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2105913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105913 prefixEnd_2105913 := by exact prefixLift 2105913
  have htrace : WordTrace (prefixWord ++ tailWord_2105913) baseStart_2105913 baseEnd_2105913 := by
    simpa [prefixWord, tailWord_2105913, baseEnd_2105913] using wordTrace_append hprefix tailTrace_2105913
  have hstable : (prefixWord ++ tailWord_2105913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105913).length < 2 ^ (prefixWord ++ tailWord_2105913).sum := by decide
  have hdescent : baseEnd_2105913 < baseStart_2105913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105950 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2105950 : Nat := 118140960795 + 2105950 * 2 ^ 59
def prefixEnd_2105950 : Nat := 4983230072969 + 3 ^ 40 * 2105950 * 2
def baseEnd_2105950 : Nat := 1081364584336140694639919

theorem tailTrace_2105950 : CollatzResearch.WordTrace tailWord_2105950 prefixEnd_2105950 1081364584336140694639919 := by
  unfold tailWord_2105950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601288340063786558813413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51206871147006861647004869 9601288340063786558813413)
  ·
    refine ⟨1800241563761959979777515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9601288340063786558813413 1800241563761959979777515)
    ·
      refine ⟨2700362345642939969666273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800241563761959979777515 2700362345642939969666273)
      ·
        refine ⟨2025271759232204977249705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2700362345642939969666273 2025271759232204977249705)
        ·
          refine ⟨1518953819424153732937279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2025271759232204977249705 1518953819424153732937279)
          ·
            refine ⟨2278430729136230599405919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518953819424153732937279 2278430729136230599405919)
            ·
              refine ⟨3417646093704345899108879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278430729136230599405919 3417646093704345899108879)
              ·
                refine ⟨5126469140556518848663319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417646093704345899108879 5126469140556518848663319)
                ·
                  refine ⟨7689703710834778272994979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5126469140556518848663319 7689703710834778272994979)
                  ·
                    refine ⟨11534555566252167409492469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7689703710834778272994979 11534555566252167409492469)
                    ·
                      refine ⟨1081364584336140694639919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11534555566252167409492469 1081364584336140694639919)
                      ·
                        rfl

theorem cell23_2105950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2105950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105950 prefixEnd_2105950 := by exact prefixLift 2105950
  have htrace : WordTrace (prefixWord ++ tailWord_2105950) baseStart_2105950 baseEnd_2105950 := by
    simpa [prefixWord, tailWord_2105950, baseEnd_2105950] using wordTrace_append hprefix tailTrace_2105950
  have hstable : (prefixWord ++ tailWord_2105950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105950).length < 2 ^ (prefixWord ++ tailWord_2105950).sum := by decide
  have hdescent : baseEnd_2105950 < baseStart_2105950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105952 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2]
def baseStart_2105952 : Nat := 118140960795 + 2105952 * 2 ^ 59
def prefixEnd_2105952 : Nat := 4983230072969 + 3 ^ 40 * 2105952 * 2
def baseEnd_2105952 : Nat := 1081365611297449686814909

theorem tailTrace_2105952 : CollatzResearch.WordTrace tailWord_2105952 prefixEnd_2105952 1081365611297449686814909 := by
  unfold tailWord_2105952
  simp only [CollatzResearch.WordTrace]
  refine ⟨38405189833251523406040055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51206919777668697874720073 38405189833251523406040055)
  ·
    refine ⟨57607784749877285109060083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38405189833251523406040055 57607784749877285109060083)
    ·
      refine ⟨86411677124815927663590125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57607784749877285109060083 86411677124815927663590125)
      ·
        refine ⟨32404378921805972873846297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86411677124815927663590125 32404378921805972873846297)
        ·
          refine ⟨24303284191354479655384723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32404378921805972873846297 24303284191354479655384723)
          ·
            refine ⟨36454926287031719483077085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24303284191354479655384723 36454926287031719483077085)
            ·
              refine ⟨13670597357636894806153907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36454926287031719483077085 13670597357636894806153907)
              ·
                refine ⟨20505896036455342209230861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13670597357636894806153907 20505896036455342209230861)
                ·
                  refine ⟨7689711013670753328461573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20505896036455342209230861 7689711013670753328461573)
                  ·
                    refine ⟨1441820815063266249086545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7689711013670753328461573 1441820815063266249086545)
                    ·
                      refine ⟨1081365611297449686814909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441820815063266249086545 1081365611297449686814909)
                      ·
                        rfl

theorem cell23_2105952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_2105952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105952 prefixEnd_2105952 := by exact prefixLift 2105952
  have htrace : WordTrace (prefixWord ++ tailWord_2105952) baseStart_2105952 baseEnd_2105952 := by
    simpa [prefixWord, tailWord_2105952, baseEnd_2105952] using wordTrace_append hprefix tailTrace_2105952
  have hstable : (prefixWord ++ tailWord_2105952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105952).length < 2 ^ (prefixWord ++ tailWord_2105952).sum := by decide
  have hdescent : baseEnd_2105952 < baseStart_2105952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105955 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2105955 : Nat := 118140960795 + 2105955 * 2 ^ 59
def prefixEnd_2105955 : Nat := 4983230072969 + 3 ^ 40 * 2105955 * 2
def baseEnd_2105955 : Nat := 1081367151739413175077395

theorem tailTrace_2105955 : CollatzResearch.WordTrace tailWord_2105955 prefixEnd_2105955 1081367151739413175077395 := by
  unfold tailWord_2105955
  simp only [CollatzResearch.WordTrace]
  refine ⟨76810489085492178324439319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51206992723661452216292879 76810489085492178324439319)
  ·
    refine ⟨115215733628238267486658979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76810489085492178324439319 115215733628238267486658979)
    ·
      refine ⟨172823600442357401229988469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115215733628238267486658979 172823600442357401229988469)
      ·
        refine ⟨16202212541471006365311419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172823600442357401229988469 16202212541471006365311419)
        ·
          refine ⟨24303318812206509547967129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16202212541471006365311419 24303318812206509547967129)
          ·
            refine ⟨18227489109154882160975347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24303318812206509547967129 18227489109154882160975347)
            ·
              refine ⟨27341233663732323241463021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18227489109154882160975347 27341233663732323241463021)
              ·
                refine ⟨10252962623899621215548633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27341233663732323241463021 10252962623899621215548633)
                ·
                  refine ⟨7689721967924715911661475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10252962623899621215548633 7689721967924715911661475)
                  ·
                    refine ⟨11534582951887073867492213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7689721967924715911661475 11534582951887073867492213)
                    ·
                      refine ⟨1081367151739413175077395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11534582951887073867492213 1081367151739413175077395)
                      ·
                        rfl

theorem cell23_2105955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2105955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105955 prefixEnd_2105955 := by exact prefixLift 2105955
  have htrace : WordTrace (prefixWord ++ tailWord_2105955) baseStart_2105955 baseEnd_2105955 := by
    simpa [prefixWord, tailWord_2105955, baseEnd_2105955] using wordTrace_append hprefix tailTrace_2105955
  have hstable : (prefixWord ++ tailWord_2105955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105955).length < 2 ^ (prefixWord ++ tailWord_2105955).sum := by decide
  have hdescent : baseEnd_2105955 < baseStart_2105955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105956 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_2105956 : Nat := 118140960795 + 2105956 * 2 ^ 59
def prefixEnd_2105956 : Nat := 4983230072969 + 3 ^ 40 * 2105956 * 2
def baseEnd_2105956 : Nat := 1081367665220067671164891

theorem tailTrace_2105956 : CollatzResearch.WordTrace tailWord_2105956 prefixEnd_2105956 1081367665220067671164891 := by
  unfold tailWord_2105956
  simp only [CollatzResearch.WordTrace]
  refine ⟨38405262779244277747612861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51207017038992370330150481 38405262779244277747612861)
  ·
    refine ⟨14401973542216604155354823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38405262779244277747612861 14401973542216604155354823)
    ·
      refine ⟨21602960313324906233032235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401973542216604155354823 21602960313324906233032235)
      ·
        refine ⟨32404440469987359349548353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21602960313324906233032235 32404440469987359349548353)
        ·
          refine ⟨24303330352490519512161265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32404440469987359349548353 24303330352490519512161265)
          ·
            refine ⟨18227497764367889634120949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24303330352490519512161265 18227497764367889634120949)
            ·
              refine ⟨1708827915409489653198839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18227497764367889634120949 1708827915409489653198839)
              ·
                refine ⟨2563241873114234479798259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708827915409489653198839 2563241873114234479798259)
                ·
                  refine ⟨3844862809671351719697389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563241873114234479798259 3844862809671351719697389)
                  ·
                    refine ⟨1441823553626756894886521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3844862809671351719697389 1441823553626756894886521)
                    ·
                      refine ⟨1081367665220067671164891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441823553626756894886521 1081367665220067671164891)
                      ·
                        rfl

theorem cell23_2105956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_2105956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2105956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2105956 prefixEnd_2105956 := by exact prefixLift 2105956
  have htrace : WordTrace (prefixWord ++ tailWord_2105956) baseStart_2105956 baseEnd_2105956 := by
    simpa [prefixWord, tailWord_2105956, baseEnd_2105956] using wordTrace_append hprefix tailTrace_2105956
  have hstable : (prefixWord ++ tailWord_2105956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105956).length < 2 ^ (prefixWord ++ tailWord_2105956).sum := by decide
  have hdescent : baseEnd_2105956 < baseStart_2105956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106025 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_2106025 : Nat := 118140960795 + 2106025 * 2 ^ 59
def prefixEnd_2106025 : Nat := 4983230072969 + 3 ^ 40 * 2106025 * 2
def baseEnd_2106025 : Nat := 1081403095385227901202073

theorem tailTrace_2106025 : CollatzResearch.WordTrace tailWord_2106025 prefixEnd_2106025 1081403095385227901202073 := by
  unfold tailWord_2106025
  simp only [CollatzResearch.WordTrace]
  refine ⟨76813042195238580279487529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51208694796825720186325019 76813042195238580279487529)
  ·
    refine ⟨57609781646428935209615647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76813042195238580279487529 57609781646428935209615647)
    ·
      refine ⟨86414672469643402814423471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57609781646428935209615647 86414672469643402814423471)
      ·
        refine ⟨129622008704465104221635207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86414672469643402814423471 129622008704465104221635207)
        ·
          refine ⟨194433013056697656332452811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129622008704465104221635207 194433013056697656332452811)
          ·
            refine ⟨291649519585046484498679217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194433013056697656332452811 291649519585046484498679217)
            ·
              refine ⟨218737139688784863374009413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291649519585046484498679217 218737139688784863374009413)
              ·
                refine ⟨41013213691647161882626765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218737139688784863374009413 41013213691647161882626765)
                ·
                  refine ⟨15379955134367685705985037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41013213691647161882626765 15379955134367685705985037)
                  ·
                    refine ⟨5767483175387882139744389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15379955134367685705985037 5767483175387882139744389)
                    ·
                      refine ⟨1081403095385227901202073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5767483175387882139744389 1081403095385227901202073)
                      ·
                        rfl

theorem cell23_2106025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_2106025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106025 prefixEnd_2106025 := by exact prefixLift 2106025
  have htrace : WordTrace (prefixWord ++ tailWord_2106025) baseStart_2106025 baseEnd_2106025 := by
    simpa [prefixWord, tailWord_2106025, baseEnd_2106025] using wordTrace_append hprefix tailTrace_2106025
  have hstable : (prefixWord ++ tailWord_2106025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106025).length < 2 ^ (prefixWord ++ tailWord_2106025).sum := by decide
  have hdescent : baseEnd_2106025 < baseStart_2106025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106026 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_2106026 : Nat := 118140960795 + 2106026 * 2 ^ 59
def prefixEnd_2106026 : Nat := 4983230072969 + 3 ^ 40 * 2106026 * 2
def baseEnd_2106026 : Nat := 120155956540653599698841

theorem tailTrace_2106026 : CollatzResearch.WordTrace tailWord_2106026 prefixEnd_2106026 120155956540653599698841 := by
  unfold tailWord_2106026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19203269667058739362568483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51208719112156638300182621 19203269667058739362568483)
  ·
    refine ⟨28804904500588109043852725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19203269667058739362568483 28804904500588109043852725)
    ·
      refine ⟨2700459796930135222861193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28804904500588109043852725 2700459796930135222861193)
      ·
        refine ⟨2025344847697601417145895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2700459796930135222861193 2025344847697601417145895)
        ·
          refine ⟨3038017271546402125718843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025344847697601417145895 3038017271546402125718843)
          ·
            refine ⟨4557025907319603188578265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038017271546402125718843 4557025907319603188578265)
            ·
              refine ⟨3417769430489702391433699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4557025907319603188578265 3417769430489702391433699)
              ·
                refine ⟨5126654145734553587150549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417769430489702391433699 5126654145734553587150549)
                ·
                  refine ⟨120155956540653599698841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5126654145734553587150549 120155956540653599698841)
                  ·
                    rfl

theorem cell23_2106026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_2106026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106026 prefixEnd_2106026 := by exact prefixLift 2106026
  have htrace : WordTrace (prefixWord ++ tailWord_2106026) baseStart_2106026 baseEnd_2106026 := by
    simpa [prefixWord, tailWord_2106026, baseEnd_2106026] using wordTrace_append hprefix tailTrace_2106026
  have hstable : (prefixWord ++ tailWord_2106026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106026).length < 2 ^ (prefixWord ++ tailWord_2106026).sum := by decide
  have hdescent : baseEnd_2106026 < baseStart_2106026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106055 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2106055 : Nat := 118140960795 + 2106055 * 2 ^ 59
def prefixEnd_2106055 : Nat := 4983230072969 + 3 ^ 40 * 2106055 * 2
def baseEnd_2106055 : Nat := 1081418499804862783826935

theorem tailTrace_2106055 : CollatzResearch.WordTrace tailWord_2106055 prefixEnd_2106055 1081418499804862783826935 := by
  unfold tailWord_2106055
  simp only [CollatzResearch.WordTrace]
  refine ⟨76814136385129895403079619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51209424256753263602053079 76814136385129895403079619)
  ·
    refine ⟨115221204577694843104619429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76814136385129895403079619 115221204577694843104619429)
    ·
      refine ⟨21603975858317783082116143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115221204577694843104619429 21603975858317783082116143)
      ·
        refine ⟨32405963787476674623174215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21603975858317783082116143 32405963787476674623174215)
        ·
          refine ⟨48608945681215011934761323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32405963787476674623174215 48608945681215011934761323)
          ·
            refine ⟨72913418521822517902141985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48608945681215011934761323 72913418521822517902141985)
            ·
              refine ⟨54685063891366888426606489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72913418521822517902141985 54685063891366888426606489)
              ·
                refine ⟨41013797918525166319954867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54685063891366888426606489 41013797918525166319954867)
                ·
                  refine ⟨61520696877787749479932301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41013797918525166319954867 61520696877787749479932301)
                  ·
                    refine ⟨23070261329170406054974613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61520696877787749479932301 23070261329170406054974613)
                    ·
                      refine ⟨1081418499804862783826935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23070261329170406054974613 1081418499804862783826935)
                      ·
                        rfl

theorem cell23_2106055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2106055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106055 prefixEnd_2106055 := by exact prefixLift 2106055
  have htrace : WordTrace (prefixWord ++ tailWord_2106055) baseStart_2106055 baseEnd_2106055 := by
    simpa [prefixWord, tailWord_2106055, baseEnd_2106055] using wordTrace_append hprefix tailTrace_2106055
  have hstable : (prefixWord ++ tailWord_2106055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106055).length < 2 ^ (prefixWord ++ tailWord_2106055).sum := by decide
  have hdescent : baseEnd_2106055 < baseStart_2106055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106065 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 10]
def baseStart_2106065 : Nat := 118140960795 + 2106065 * 2 ^ 59
def prefixEnd_2106065 : Nat := 4983230072969 + 3 ^ 40 * 2106065 * 2
def baseEnd_2106065 : Nat := 120158181623489749411321

theorem tailTrace_2106065 : CollatzResearch.WordTrace tailWord_2106065 prefixEnd_2106065 120158181623489749411321 := by
  unfold tailWord_2106065
  simp only [CollatzResearch.WordTrace]
  refine ⟨76814501115093667110943649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51209667410062444740629099 76814501115093667110943649)
  ·
    refine ⟨57610875836320250333207737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76814501115093667110943649 57610875836320250333207737)
    ·
      refine ⟨43208156877240187749905803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57610875836320250333207737 43208156877240187749905803)
      ·
        refine ⟨64812235315860281624858705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43208156877240187749905803 64812235315860281624858705)
        ·
          refine ⟨48609176486895211218644029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64812235315860281624858705 48609176486895211218644029)
          ·
            refine ⟨18228441182585704206991511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48609176486895211218644029 18228441182585704206991511)
            ·
              refine ⟨27342661773878556310487267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18228441182585704206991511 27342661773878556310487267)
              ·
                refine ⟨41013992660817834465730901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27342661773878556310487267 41013992660817834465730901)
                ·
                  refine ⟨120158181623489749411321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41013992660817834465730901 120158181623489749411321)
                  ·
                    rfl

theorem cell23_2106065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_2106065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106065 prefixEnd_2106065 := by exact prefixLift 2106065
  have htrace : WordTrace (prefixWord ++ tailWord_2106065) baseStart_2106065 baseEnd_2106065 := by
    simpa [prefixWord, tailWord_2106065, baseEnd_2106065] using wordTrace_append hprefix tailTrace_2106065
  have hstable : (prefixWord ++ tailWord_2106065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106065).length < 2 ^ (prefixWord ++ tailWord_2106065).sum := by decide
  have hdescent : baseEnd_2106065 < baseStart_2106065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106076 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2106076 : Nat := 118140960795 + 2106076 * 2 ^ 59
def prefixEnd_2106076 : Nat := 4983230072969 + 3 ^ 40 * 2106076 * 2
def baseEnd_2106076 : Nat := 1081429282898607201664339

theorem tailTrace_2106076 : CollatzResearch.WordTrace tailWord_2106076 prefixEnd_2106076 1081429282898607201664339 := by
  unfold tailWord_2106076
  simp only [CollatzResearch.WordTrace]
  refine ⟨38407451159026907994797041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51209934878702543993062721 38407451159026907994797041)
  ·
    refine ⟨28805588369270180996097781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38407451159026907994797041 28805588369270180996097781)
    ·
      refine ⟨2700523909619079468384167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28805588369270180996097781 2700523909619079468384167)
      ·
        refine ⟨4050785864428619202576251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700523909619079468384167 4050785864428619202576251)
        ·
          refine ⟨6076178796642928803864377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4050785864428619202576251 6076178796642928803864377)
          ·
            refine ⟨4557134097482196602898283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6076178796642928803864377 4557134097482196602898283)
            ·
              refine ⟨6835701146223294904347425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557134097482196602898283 6835701146223294904347425)
              ·
                refine ⟨5126775859667471178260569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6835701146223294904347425 5126775859667471178260569)
                ·
                  refine ⟨3845081894750603383695427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5126775859667471178260569 3845081894750603383695427)
                  ·
                    refine ⟨5767622842125905075543141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3845081894750603383695427 5767622842125905075543141)
                    ·
                      refine ⟨1081429282898607201664339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5767622842125905075543141 1081429282898607201664339)
                      ·
                        rfl

theorem cell23_2106076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2106076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106076 prefixEnd_2106076 := by exact prefixLift 2106076
  have htrace : WordTrace (prefixWord ++ tailWord_2106076) baseStart_2106076 baseEnd_2106076 := by
    simpa [prefixWord, tailWord_2106076, baseEnd_2106076] using wordTrace_append hprefix tailTrace_2106076
  have hstable : (prefixWord ++ tailWord_2106076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106076).length < 2 ^ (prefixWord ++ tailWord_2106076).sum := by decide
  have hdescent : baseEnd_2106076 < baseStart_2106076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106079 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2106079 : Nat := 118140960795 + 2106079 * 2 ^ 59
def prefixEnd_2106079 : Nat := 4983230072969 + 3 ^ 40 * 2106079 * 2
def baseEnd_2106079 : Nat := 1081430823340570689926825

theorem tailTrace_2106079 : CollatzResearch.WordTrace tailWord_2106079 prefixEnd_2106079 1081430823340570689926825 := by
  unfold tailWord_2106079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76815011737042947501953291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51210007824695298334635527 76815011737042947501953291)
  ·
    refine ⟨115222517605564421252929937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76815011737042947501953291 115222517605564421252929937)
    ·
      refine ⟨86416888204173315939697453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115222517605564421252929937 86416888204173315939697453)
      ·
        refine ⟨32406333076564993477386545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86416888204173315939697453 32406333076564993477386545)
        ·
          refine ⟨24304749807423745108039909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32406333076564993477386545 24304749807423745108039909)
          ·
            refine ⟨4557140588891952207757483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24304749807423745108039909 4557140588891952207757483)
            ·
              refine ⟨6835710883337928311636225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557140588891952207757483 6835710883337928311636225)
              ·
                refine ⟨5126783162503446233727169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6835710883337928311636225 5126783162503446233727169)
                ·
                  refine ⟨3845087371877584675295377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5126783162503446233727169 3845087371877584675295377)
                  ·
                    refine ⟨2883815528908188506471533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845087371877584675295377 2883815528908188506471533)
                    ·
                      refine ⟨1081430823340570689926825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883815528908188506471533 1081430823340570689926825)
                      ·
                        rfl

theorem cell23_2106079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2106079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106079 prefixEnd_2106079 := by exact prefixLift 2106079
  have htrace : WordTrace (prefixWord ++ tailWord_2106079) baseStart_2106079 baseEnd_2106079 := by
    simpa [prefixWord, tailWord_2106079, baseEnd_2106079] using wordTrace_append hprefix tailTrace_2106079
  have hstable : (prefixWord ++ tailWord_2106079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106079).length < 2 ^ (prefixWord ++ tailWord_2106079).sum := by decide
  have hdescent : baseEnd_2106079 < baseStart_2106079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106109 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2106109 : Nat := 118140960795 + 2106109 * 2 ^ 59
def prefixEnd_2106109 : Nat := 4983230072969 + 3 ^ 40 * 2106109 * 2
def baseEnd_2106109 : Nat := 1081446227760205572551687

theorem tailTrace_2106109 : CollatzResearch.WordTrace tailWord_2106109 prefixEnd_2106109 1081446227760205572551687 := by
  unfold tailWord_2106109
  simp only [CollatzResearch.WordTrace]
  refine ⟨76816105926934262625545381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51210737284622841750363587 76816105926934262625545381)
  ·
    refine ⟨14403019861300174242289759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76816105926934262625545381 14403019861300174242289759)
    ·
      refine ⟨21604529791950261363434639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14403019861300174242289759 21604529791950261363434639)
      ·
        refine ⟨32406794687925392045151959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21604529791950261363434639 32406794687925392045151959)
        ·
          refine ⟨48610192031888088067727939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32406794687925392045151959 48610192031888088067727939)
          ·
            refine ⟨72915288047832132101591909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48610192031888088067727939 72915288047832132101591909)
            ·
              refine ⟨13671616508968524769048483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72915288047832132101591909 13671616508968524769048483)
              ·
                refine ⟨20507424763452787153572725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13671616508968524769048483 20507424763452787153572725)
                ·
                  refine ⟨1922571071573698795647443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20507424763452787153572725 1922571071573698795647443)
                  ·
                    refine ⟨2883856607360548193471165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922571071573698795647443 2883856607360548193471165)
                    ·
                      refine ⟨1081446227760205572551687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883856607360548193471165 1081446227760205572551687)
                      ·
                        rfl

theorem cell23_2106109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2106109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106109 prefixEnd_2106109 := by exact prefixLift 2106109
  have htrace : WordTrace (prefixWord ++ tailWord_2106109) baseStart_2106109 baseEnd_2106109 := by
    simpa [prefixWord, tailWord_2106109, baseEnd_2106109] using wordTrace_append hprefix tailTrace_2106109
  have hstable : (prefixWord ++ tailWord_2106109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106109).length < 2 ^ (prefixWord ++ tailWord_2106109).sum := by decide
  have hdescent : baseEnd_2106109 < baseStart_2106109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106143 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 1, 1, 3]
def baseStart_2106143 : Nat := 118140960795 + 2106143 * 2 ^ 59
def prefixEnd_2106143 : Nat := 4983230072969 + 3 ^ 40 * 2106143 * 2
def baseEnd_2106143 : Nat := 1081463686102458439526531

theorem tailTrace_2106143 : CollatzResearch.WordTrace tailWord_2106143 prefixEnd_2106143 1081463686102458439526531 := by
  unfold tailWord_2106143
  simp only [CollatzResearch.WordTrace]
  refine ⟨76817346008811086432283083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51211564005874057621522055 76817346008811086432283083)
  ·
    refine ⟨115226019013216629648424625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76817346008811086432283083 115226019013216629648424625)
    ·
      refine ⟨86419514259912472236318469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115226019013216629648424625 86419514259912472236318469)
      ·
        refine ⟨16203658923733588544309713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86419514259912472236318469 16203658923733588544309713)
        ·
          refine ⟨12152744192800191408232285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16203658923733588544309713 12152744192800191408232285)
          ·
            refine ⟨4557279072300071778087107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12152744192800191408232285 4557279072300071778087107)
            ·
              refine ⟨6835918608450107667130661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557279072300071778087107 6835918608450107667130661)
              ·
                refine ⟨1281734739084395187586999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6835918608450107667130661 1281734739084395187586999)
                ·
                  refine ⟨1922602108626592781380499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281734739084395187586999 1922602108626592781380499)
                  ·
                    refine ⟨2883903162939889172070749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922602108626592781380499 2883903162939889172070749)
                    ·
                      refine ⟨1081463686102458439526531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883903162939889172070749 1081463686102458439526531)
                      ·
                        rfl

theorem cell23_2106143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_2106143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106143 prefixEnd_2106143 := by exact prefixLift 2106143
  have htrace : WordTrace (prefixWord ++ tailWord_2106143) baseStart_2106143 baseEnd_2106143 := by
    simpa [prefixWord, tailWord_2106143, baseEnd_2106143] using wordTrace_append hprefix tailTrace_2106143
  have hstable : (prefixWord ++ tailWord_2106143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106143).length < 2 ^ (prefixWord ++ tailWord_2106143).sum := by decide
  have hdescent : baseEnd_2106143 < baseStart_2106143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106170 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_2106170 : Nat := 118140960795 + 2106170 * 2 ^ 59
def prefixEnd_2106170 : Nat := 4983230072969 + 3 ^ 40 * 2106170 * 2
def baseEnd_2106170 : Nat := 1081477550080129833888907

theorem tailTrace_2106170 : CollatzResearch.WordTrace tailWord_2106170 prefixEnd_2106170 1081477550080129833888907 := by
  unfold tailWord_2106170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19204582694928317510878991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51212220519808846695677309 19204582694928317510878991)
  ·
    refine ⟨28806874042392476266318487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19204582694928317510878991 28806874042392476266318487)
    ·
      refine ⟨43210311063588714399477731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28806874042392476266318487 43210311063588714399477731)
      ·
        refine ⟨64815466595383071599216597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43210311063588714399477731 64815466595383071599216597)
        ·
          refine ⟨1519112498329290740606639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64815466595383071599216597 1519112498329290740606639)
          ·
            refine ⟨2278668747493936110909959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519112498329290740606639 2278668747493936110909959)
            ·
              refine ⟨3418003121240904166364939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278668747493936110909959 3418003121240904166364939)
              ·
                refine ⟨5127004681861356249547409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418003121240904166364939 5127004681861356249547409)
                ·
                  refine ⟨3845253511396017187160557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5127004681861356249547409 3845253511396017187160557)
                  ·
                    refine ⟨1441970066773506445185209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3845253511396017187160557 1441970066773506445185209)
                    ·
                      refine ⟨1081477550080129833888907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441970066773506445185209 1081477550080129833888907)
                      ·
                        rfl

theorem cell23_2106170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_2106170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106170 prefixEnd_2106170 := by exact prefixLift 2106170
  have htrace : WordTrace (prefixWord ++ tailWord_2106170) baseStart_2106170 baseEnd_2106170 := by
    simpa [prefixWord, tailWord_2106170, baseEnd_2106170] using wordTrace_append hprefix tailTrace_2106170
  have hstable : (prefixWord ++ tailWord_2106170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106170).length < 2 ^ (prefixWord ++ tailWord_2106170).sum := by decide
  have hdescent : baseEnd_2106170 < baseStart_2106170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106177 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2106177 : Nat := 118140960795 + 2106177 * 2 ^ 59
def prefixEnd_2106177 : Nat := 4983230072969 + 3 ^ 40 * 2106177 * 2
def baseEnd_2106177 : Nat := 1081481144444711306501375

theorem tailTrace_2106177 : CollatzResearch.WordTrace tailWord_2106177 prefixEnd_2106177 1081481144444711306501375 := by
  unfold tailWord_2106177
  simp only [CollatzResearch.WordTrace]
  refine ⟨76818586090687910239020785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51212390727125273492680523 76818586090687910239020785)
  ·
    refine ⟨57613939568015932679265589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76818586090687910239020785 57613939568015932679265589)
    ·
      refine ⟨5401306834501493688681149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57613939568015932679265589 5401306834501493688681149)
      ·
        refine ⟨2025490062938060133255431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5401306834501493688681149 2025490062938060133255431)
        ·
          refine ⟨3038235094407090199883147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025490062938060133255431 3038235094407090199883147)
          ·
            refine ⟨4557352641610635299824721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038235094407090199883147 4557352641610635299824721)
            ·
              refine ⟨3418014481207976474868541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4557352641610635299824721 3418014481207976474868541)
              ·
                refine ⟨1281755430452991178075703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3418014481207976474868541 1281755430452991178075703)
                ·
                  refine ⟨1922633145679486767113555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281755430452991178075703 1922633145679486767113555)
                  ·
                    refine ⟨2883949718519230150670333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922633145679486767113555 2883949718519230150670333)
                    ·
                      refine ⟨1081481144444711306501375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2883949718519230150670333 1081481144444711306501375)
                      ·
                        rfl

theorem cell23_2106177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2106177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106177 prefixEnd_2106177 := by exact prefixLift 2106177
  have htrace : WordTrace (prefixWord ++ tailWord_2106177) baseStart_2106177 baseEnd_2106177 := by
    simpa [prefixWord, tailWord_2106177, baseEnd_2106177] using wordTrace_append hprefix tailTrace_2106177
  have hstable : (prefixWord ++ tailWord_2106177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106177).length < 2 ^ (prefixWord ++ tailWord_2106177).sum := by decide
  have hdescent : baseEnd_2106177 < baseStart_2106177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106193 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_2106193 : Nat := 118140960795 + 2106193 * 2 ^ 59
def prefixEnd_2106193 : Nat := 4983230072969 + 3 ^ 40 * 2106193 * 2
def baseEnd_2106193 : Nat := 360496453378394414633767

theorem tailTrace_2106193 : CollatzResearch.WordTrace tailWord_2106193 prefixEnd_2106193 360496453378394414633767 := by
  unfold tailWord_2106193
  simp only [CollatzResearch.WordTrace]
  refine ⟨76819169658629944971603233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51212779772419963314402155 76819169658629944971603233)
  ·
    refine ⟨57614377243972458728702425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76819169658629944971603233 57614377243972458728702425)
    ·
      refine ⟨43210782932979344046526819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57614377243972458728702425 43210782932979344046526819)
      ·
        refine ⟨64816174399469016069790229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43210782932979344046526819 64816174399469016069790229)
        ·
          refine ⟨3038258174975110128271417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64816174399469016069790229 3038258174975110128271417)
          ·
            refine ⟨2278693631231332596203563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038258174975110128271417 2278693631231332596203563)
            ·
              refine ⟨3418040446846998894305345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278693631231332596203563 3418040446846998894305345)
              ·
                refine ⟨2563530335135249170729009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3418040446846998894305345 2563530335135249170729009)
                ·
                  refine ⟨1922647751351436878046757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2563530335135249170729009 1922647751351436878046757)
                  ·
                    refine ⟨360496453378394414633767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922647751351436878046757 360496453378394414633767)
                    ·
                      rfl

theorem cell23_2106193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_2106193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106193 prefixEnd_2106193 := by exact prefixLift 2106193
  have htrace : WordTrace (prefixWord ++ tailWord_2106193) baseStart_2106193 baseEnd_2106193 := by
    simpa [prefixWord, tailWord_2106193, baseEnd_2106193] using wordTrace_append hprefix tailTrace_2106193
  have hstable : (prefixWord ++ tailWord_2106193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106193).length < 2 ^ (prefixWord ++ tailWord_2106193).sum := by decide
  have hdescent : baseEnd_2106193 < baseStart_2106193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106209 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_2106209 : Nat := 118140960795 + 2106209 * 2 ^ 59
def prefixEnd_2106209 : Nat := 4983230072969 + 3 ^ 40 * 2106209 * 2
def baseEnd_2106209 : Nat := 1081497575825655181301227

theorem tailTrace_2106209 : CollatzResearch.WordTrace tailWord_2106209 prefixEnd_2106209 1081497575825655181301227 := by
  unfold tailWord_2106209
  simp only [CollatzResearch.WordTrace]
  refine ⟨76819753226571979704185681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51213168817714653136123787 76819753226571979704185681)
  ·
    refine ⟨57614814919928984778139261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76819753226571979704185681 57614814919928984778139261)
    ·
      refine ⟨21605555594973369291802223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57614814919928984778139261 21605555594973369291802223)
      ·
        refine ⟨32408333392460053937703335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21605555594973369291802223 32408333392460053937703335)
        ·
          refine ⟨48612500088690080906555003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32408333392460053937703335 48612500088690080906555003)
          ·
            refine ⟨72918750133035121359832505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48612500088690080906555003 72918750133035121359832505)
            ·
              refine ⟨54689062599776341019874379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72918750133035121359832505 54689062599776341019874379)
              ·
                refine ⟨82033593899664511529811569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54689062599776341019874379 82033593899664511529811569)
                ·
                  refine ⟨61525195424748383647358677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82033593899664511529811569 61525195424748383647358677)
                  ·
                    refine ⟨1441996767767540241734969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61525195424748383647358677 1441996767767540241734969)
                    ·
                      refine ⟨1081497575825655181301227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1441996767767540241734969 1081497575825655181301227)
                      ·
                        rfl

theorem cell23_2106209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_2106209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106209 prefixEnd_2106209 := by exact prefixLift 2106209
  have htrace : WordTrace (prefixWord ++ tailWord_2106209) baseStart_2106209 baseEnd_2106209 := by
    simpa [prefixWord, tailWord_2106209, baseEnd_2106209] using wordTrace_append hprefix tailTrace_2106209
  have hstable : (prefixWord ++ tailWord_2106209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106209).length < 2 ^ (prefixWord ++ tailWord_2106209).sum := by decide
  have hdescent : baseEnd_2106209 < baseStart_2106209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106210 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2106210 : Nat := 118140960795 + 2106210 * 2 ^ 59
def prefixEnd_2106210 : Nat := 4983230072969 + 3 ^ 40 * 2106210 * 2
def baseEnd_2106210 : Nat := 360499363102103225796241

theorem tailTrace_2106210 : CollatzResearch.WordTrace tailWord_2106210 prefixEnd_2106210 360499363102103225796241 := by
  unfold tailWord_2106210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19204947424892089218743021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51213193133045571249981389 19204947424892089218743021)
  ·
    refine ⟨7201855284334533457028633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19204947424892089218743021 7201855284334533457028633)
    ·
      refine ⟨5401391463250900092771475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7201855284334533457028633 5401391463250900092771475)
      ·
        refine ⟨8102087194876350139157213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401391463250900092771475 8102087194876350139157213)
        ·
          refine ⟨3038282698078631302183955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8102087194876350139157213 3038282698078631302183955)
          ·
            refine ⟨4557424047117946953275933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038282698078631302183955 4557424047117946953275933)
            ·
              refine ⟨1709034017669230107478475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4557424047117946953275933 1709034017669230107478475)
              ·
                refine ⟨2563551026503845161217713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709034017669230107478475 2563551026503845161217713)
                ·
                  refine ⟨1922663269877883870913285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2563551026503845161217713 1922663269877883870913285)
                  ·
                    refine ⟨360499363102103225796241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922663269877883870913285 360499363102103225796241)
                    ·
                      rfl

theorem cell23_2106210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2106210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106210 prefixEnd_2106210 := by exact prefixLift 2106210
  have htrace : WordTrace (prefixWord ++ tailWord_2106210) baseStart_2106210 baseEnd_2106210 := by
    simpa [prefixWord, tailWord_2106210, baseEnd_2106210] using wordTrace_append hprefix tailTrace_2106210
  have hstable : (prefixWord ++ tailWord_2106210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106210).length < 2 ^ (prefixWord ++ tailWord_2106210).sum := by decide
  have hdescent : baseEnd_2106210 < baseStart_2106210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106216 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2106216 : Nat := 118140960795 + 2106216 * 2 ^ 59
def prefixEnd_2106216 : Nat := 4983230072969 + 3 ^ 40 * 2106216 * 2
def baseEnd_2106216 : Nat := 1081501170190236653913695

theorem tailTrace_2106216 : CollatzResearch.WordTrace tailWord_2106216 prefixEnd_2106216 1081501170190236653913695 := by
  unfold tailWord_2106216
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410004268773309949845251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51213339025031079933127001 38410004268773309949845251)
  ·
    refine ⟨57615006403159964924767877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38410004268773309949845251 57615006403159964924767877)
    ·
      refine ⟨10802813700592493423393977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57615006403159964924767877 10802813700592493423393977)
      ·
        refine ⟨8102110275444370067545483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10802813700592493423393977 8102110275444370067545483)
        ·
          refine ⟨12153165413166555101318225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8102110275444370067545483 12153165413166555101318225)
          ·
            refine ⟨9114874059874916325988669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12153165413166555101318225 9114874059874916325988669)
            ·
              refine ⟨3418077772453093622245751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9114874059874916325988669 3418077772453093622245751)
              ·
                refine ⟨5127116658679640433368627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418077772453093622245751 5127116658679640433368627)
                ·
                  refine ⟨7690674988019460650052941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5127116658679640433368627 7690674988019460650052941)
                  ·
                    refine ⟨2884003120507297743769853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7690674988019460650052941 2884003120507297743769853)
                    ·
                      refine ⟨1081501170190236653913695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2884003120507297743769853 1081501170190236653913695)
                      ·
                        rfl

theorem cell23_2106216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2106216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106216 prefixEnd_2106216 := by exact prefixLift 2106216
  have htrace : WordTrace (prefixWord ++ tailWord_2106216) baseStart_2106216 baseEnd_2106216 := by
    simpa [prefixWord, tailWord_2106216, baseEnd_2106216] using wordTrace_append hprefix tailTrace_2106216
  have hstable : (prefixWord ++ tailWord_2106216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106216).length < 2 ^ (prefixWord ++ tailWord_2106216).sum := by decide
  have hdescent : baseEnd_2106216 < baseStart_2106216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106226 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2106226 : Nat := 118140960795 + 2106226 * 2 ^ 59
def prefixEnd_2106226 : Nat := 4983230072969 + 3 ^ 40 * 2106226 * 2
def baseEnd_2106226 : Nat := 1081506304996781614788649

theorem tailTrace_2106226 : CollatzResearch.WordTrace tailWord_2106226 prefixEnd_2106226 1081506304996781614788649 := by
  unfold tailWord_2106226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19205093316877597901888633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51213582178340261071703021 19205093316877597901888633)
  ·
    refine ⟨14403819987658198426416475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19205093316877597901888633 14403819987658198426416475)
    ·
      refine ⟨21605729981487297639624713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14403819987658198426416475 21605729981487297639624713)
      ·
        refine ⟨16204297486115473229718535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21605729981487297639624713 16204297486115473229718535)
        ·
          refine ⟨24306446229173209844577803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16204297486115473229718535 24306446229173209844577803)
          ·
            refine ⟨36459669343759814766866705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24306446229173209844577803 36459669343759814766866705)
            ·
              refine ⟨27344752007819861075150029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36459669343759814766866705 27344752007819861075150029)
              ·
                refine ⟨10254282002932447903181261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27344752007819861075150029 10254282002932447903181261)
                ·
                  refine ⟨3845355751099667963692973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10254282002932447903181261 3845355751099667963692973)
                  ·
                    refine ⟨1442008406662375486384865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3845355751099667963692973 1442008406662375486384865)
                    ·
                      refine ⟨1081506304996781614788649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442008406662375486384865 1081506304996781614788649)
                      ·
                        rfl

theorem cell23_2106226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2106226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106226 prefixEnd_2106226 := by exact prefixLift 2106226
  have htrace : WordTrace (prefixWord ++ tailWord_2106226) baseStart_2106226 baseEnd_2106226 := by
    simpa [prefixWord, tailWord_2106226, baseEnd_2106226] using wordTrace_append hprefix tailTrace_2106226
  have hstable : (prefixWord ++ tailWord_2106226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106226).length < 2 ^ (prefixWord ++ tailWord_2106226).sum := by decide
  have hdescent : baseEnd_2106226 < baseStart_2106226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106229 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2106229 : Nat := 118140960795 + 2106229 * 2 ^ 59
def prefixEnd_2106229 : Nat := 4983230072969 + 3 ^ 40 * 2106229 * 2
def baseEnd_2106229 : Nat := 1081507845438745103051135

theorem tailTrace_2106229 : CollatzResearch.WordTrace tailWord_2106229 prefixEnd_2106229 1081507845438745103051135 := by
  unfold tailWord_2106229
  simp only [CollatzResearch.WordTrace]
  refine ⟨76820482686499523119913741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51213655124333015413275827 76820482686499523119913741)
  ·
    refine ⟨28807681007437321169967653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76820482686499523119913741 28807681007437321169967653)
    ·
      refine ⟨5401440188894497719368935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28807681007437321169967653 5401440188894497719368935)
      ·
        refine ⟨8102160283341746579053403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401440188894497719368935 8102160283341746579053403)
        ·
          refine ⟨12153240425012619868580105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8102160283341746579053403 12153240425012619868580105)
          ·
            refine ⟨9114930318759464901435079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12153240425012619868580105 9114930318759464901435079)
            ·
              refine ⟨13672395478139197352152619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9114930318759464901435079 13672395478139197352152619)
              ·
                refine ⟨20508593217208796028228929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13672395478139197352152619 20508593217208796028228929)
                ·
                  refine ⟨15381444912906597021171697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20508593217208796028228929 15381444912906597021171697)
                  ·
                    refine ⟨11536083684679947765878773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15381444912906597021171697 11536083684679947765878773)
                    ·
                      refine ⟨1081507845438745103051135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11536083684679947765878773 1081507845438745103051135)
                      ·
                        rfl

theorem cell23_2106229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2106229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106229 prefixEnd_2106229 := by exact prefixLift 2106229
  have htrace : WordTrace (prefixWord ++ tailWord_2106229) baseStart_2106229 baseEnd_2106229 := by
    simpa [prefixWord, tailWord_2106229, baseEnd_2106229] using wordTrace_append hprefix tailTrace_2106229
  have hstable : (prefixWord ++ tailWord_2106229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106229).length < 2 ^ (prefixWord ++ tailWord_2106229).sum := by decide
  have hdescent : baseEnd_2106229 < baseStart_2106229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106232 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_2106232 : Nat := 118140960795 + 2106232 * 2 ^ 59
def prefixEnd_2106232 : Nat := 4983230072969 + 3 ^ 40 * 2106232 * 2
def baseEnd_2106232 : Nat := 360503128626902863771207

theorem tailTrace_2106232 : CollatzResearch.WordTrace tailWord_2106232 prefixEnd_2106232 360503128626902863771207 := by
  unfold tailWord_2106232
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410296052744327316136475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51213728070325769754848633 38410296052744327316136475)
  ·
    refine ⟨57615444079116490974204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38410296052744327316136475 57615444079116490974204713)
    ·
      refine ⟨43211583059337368230653535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57615444079116490974204713 43211583059337368230653535)
      ·
        refine ⟨64817374589006052345980303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43211583059337368230653535 64817374589006052345980303)
        ·
          refine ⟨97226061883509078518970455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64817374589006052345980303 97226061883509078518970455)
          ·
            refine ⟨145839092825263617778455683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97226061883509078518970455 145839092825263617778455683)
            ·
              refine ⟨218758639237895426667683525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145839092825263617778455683 218758639237895426667683525)
              ·
                refine ⟨41017244857105392500190661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218758639237895426667683525 41017244857105392500190661)
                ·
                  refine ⟨7690733410707261093785749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41017244857105392500190661 7690733410707261093785749)
                  ·
                    refine ⟨360503128626902863771207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7690733410707261093785749 360503128626902863771207)
                    ·
                      rfl

theorem cell23_2106232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_2106232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106232 prefixEnd_2106232 := by exact prefixLift 2106232
  have htrace : WordTrace (prefixWord ++ tailWord_2106232) baseStart_2106232 baseEnd_2106232 := by
    simpa [prefixWord, tailWord_2106232, baseEnd_2106232] using wordTrace_append hprefix tailTrace_2106232
  have hstable : (prefixWord ++ tailWord_2106232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106232).length < 2 ^ (prefixWord ++ tailWord_2106232).sum := by decide
  have hdescent : baseEnd_2106232 < baseStart_2106232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106256 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2]
def baseStart_2106256 : Nat := 118140960795 + 2106256 * 2 ^ 59
def prefixEnd_2106256 : Nat := 4983230072969 + 3 ^ 40 * 2106256 * 2
def baseEnd_2106256 : Nat := 1081521709416416497413511

theorem tailTrace_2106256 : CollatzResearch.WordTrace tailWord_2106256 prefixEnd_2106256 1081521709416416497413511 := by
  unfold tailWord_2106256
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410733728700853365573311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51214311638267804487431081 38410733728700853365573311)
  ·
    refine ⟨57616100593051280048359967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38410733728700853365573311 57616100593051280048359967)
    ·
      refine ⟨86424150889576920072539951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57616100593051280048359967 86424150889576920072539951)
      ·
        refine ⟨129636226334365380108809927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86424150889576920072539951 129636226334365380108809927)
        ·
          refine ⟨194454339501548070163214891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129636226334365380108809927 194454339501548070163214891)
          ·
            refine ⟨291681509252322105244822337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194454339501548070163214891 291681509252322105244822337)
            ·
              refine ⟨218761131939241578933616753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291681509252322105244822337 218761131939241578933616753)
              ·
                refine ⟨164070848954431184200212565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218761131939241578933616753 164070848954431184200212565)
                ·
                  refine ⟨1922705261184740439846241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 164070848954431184200212565 1922705261184740439846241)
                  ·
                    refine ⟨1442028945888555329884681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1922705261184740439846241 1442028945888555329884681)
                    ·
                      refine ⟨1081521709416416497413511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442028945888555329884681 1081521709416416497413511)
                      ·
                        rfl

theorem cell23_2106256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2].length) (baseStart_2106256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106256 prefixEnd_2106256 := by exact prefixLift 2106256
  have htrace : WordTrace (prefixWord ++ tailWord_2106256) baseStart_2106256 baseEnd_2106256 := by
    simpa [prefixWord, tailWord_2106256, baseEnd_2106256] using wordTrace_append hprefix tailTrace_2106256
  have hstable : (prefixWord ++ tailWord_2106256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106256).length < 2 ^ (prefixWord ++ tailWord_2106256).sum := by decide
  have hdescent : baseEnd_2106256 < baseStart_2106256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106269 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2106269 : Nat := 118140960795 + 2106269 * 2 ^ 59
def prefixEnd_2106269 : Nat := 4983230072969 + 3 ^ 40 * 2106269 * 2
def baseEnd_2106269 : Nat := 1081528384664924946550951

theorem tailTrace_2106269 : CollatzResearch.WordTrace tailWord_2106269 prefixEnd_2106269 1081528384664924946550951 := by
  unfold tailWord_2106269
  simp only [CollatzResearch.WordTrace]
  refine ⟨76821941606354609951369861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51214627737569739967579907 76821941606354609951369861)
  ·
    refine ⟨14404114051191489365881849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76821941606354609951369861 14404114051191489365881849)
    ·
      refine ⟨10803085538393617024411387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14404114051191489365881849 10803085538393617024411387)
      ·
        refine ⟨16204628307590425536617081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10803085538393617024411387 16204628307590425536617081)
        ·
          refine ⟨12153471230692819152462811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16204628307590425536617081 12153471230692819152462811)
          ·
            refine ⟨18230206846039228728694217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12153471230692819152462811 18230206846039228728694217)
            ·
              refine ⟨13672655134529421546520663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18230206846039228728694217 13672655134529421546520663)
              ·
                refine ⟨20508982701794132319780995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13672655134529421546520663 20508982701794132319780995)
                ·
                  refine ⟨30763474052691198479671493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20508982701794132319780995 30763474052691198479671493)
                  ·
                    refine ⟨5768151384879599714938405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30763474052691198479671493 5768151384879599714938405)
                    ·
                      refine ⟨1081528384664924946550951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5768151384879599714938405 1081528384664924946550951)
                      ·
                        rfl

theorem cell23_2106269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2106269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106269 prefixEnd_2106269 := by exact prefixLift 2106269
  have htrace : WordTrace (prefixWord ++ tailWord_2106269) baseStart_2106269 baseEnd_2106269 := by
    simpa [prefixWord, tailWord_2106269, baseEnd_2106269] using wordTrace_append hprefix tailTrace_2106269
  have hstable : (prefixWord ++ tailWord_2106269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106269).length < 2 ^ (prefixWord ++ tailWord_2106269).sum := by decide
  have hdescent : baseEnd_2106269 < baseStart_2106269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106316 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2106316 : Nat := 118140960795 + 2106316 * 2 ^ 59
def prefixEnd_2106316 : Nat := 4983230072969 + 3 ^ 40 * 2106316 * 2
def baseEnd_2106316 : Nat := 1081552518255686262663235

theorem tailTrace_2106316 : CollatzResearch.WordTrace tailWord_2106316 prefixEnd_2106316 1081552518255686262663235 := by
  unfold tailWord_2106316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38411827918592168489165401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51215770558122891318887201 38411827918592168489165401)
  ·
    refine ⟨28808870938944126366874051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38411827918592168489165401 28808870938944126366874051)
    ·
      refine ⟨43213306408416189550311077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28808870938944126366874051 43213306408416189550311077)
      ·
        refine ⟨8102494951578035540683327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43213306408416189550311077 8102494951578035540683327)
        ·
          refine ⟨12153742427367053311024991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8102494951578035540683327 12153742427367053311024991)
          ·
            refine ⟨18230613641050579966537487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12153742427367053311024991 18230613641050579966537487)
            ·
              refine ⟨27345920461575869949806231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18230613641050579966537487 27345920461575869949806231)
              ·
                refine ⟨41018880692363804924709347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27345920461575869949806231 41018880692363804924709347)
                ·
                  refine ⟨61528321038545707387064021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41018880692363804924709347 61528321038545707387064021)
                  ·
                    refine ⟨1442070024340915016884313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61528321038545707387064021 1442070024340915016884313)
                    ·
                      refine ⟨1081552518255686262663235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442070024340915016884313 1081552518255686262663235)
                      ·
                        rfl

theorem cell23_2106316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2106316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106316 prefixEnd_2106316 := by exact prefixLift 2106316
  have htrace : WordTrace (prefixWord ++ tailWord_2106316) baseStart_2106316 baseEnd_2106316 := by
    simpa [prefixWord, tailWord_2106316, baseEnd_2106316] using wordTrace_append hprefix tailTrace_2106316
  have hstable : (prefixWord ++ tailWord_2106316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106316).length < 2 ^ (prefixWord ++ tailWord_2106316).sum := by decide
  have hdescent : baseEnd_2106316 < baseStart_2106316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106319 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_2106319 : Nat := 118140960795 + 2106319 * 2 ^ 59
def prefixEnd_2106319 : Nat := 4983230072969 + 3 ^ 40 * 2106319 * 2
def baseEnd_2106319 : Nat := 1081554058697649750925721

theorem tailTrace_2106319 : CollatzResearch.WordTrace tailWord_2106319 prefixEnd_2106319 1081554058697649750925721 := by
  unfold tailWord_2106319
  simp only [CollatzResearch.WordTrace]
  refine ⟨76823765256173468490690011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51215843504115645660460007 76823765256173468490690011)
  ·
    refine ⟨115235647884260202736035017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76823765256173468490690011 115235647884260202736035017)
    ·
      refine ⟨86426735913195152052026263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115235647884260202736035017 86426735913195152052026263)
      ·
        refine ⟨129640103869792728078039395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86426735913195152052026263 129640103869792728078039395)
        ·
          refine ⟨194460155804689092117059093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129640103869792728078039395 194460155804689092117059093)
          ·
            refine ⟨9115319803344801192987145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 194460155804689092117059093 9115319803344801192987145)
            ·
              refine ⟨6836489852508600894740359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9115319803344801192987145 6836489852508600894740359)
              ·
                refine ⟨10254734778762901342110539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6836489852508600894740359 10254734778762901342110539)
                ·
                  refine ⟨15382102168144352013165809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10254734778762901342110539 15382102168144352013165809)
                  ·
                    refine ⟨11536576626108264009874357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15382102168144352013165809 11536576626108264009874357)
                    ·
                      refine ⟨1081554058697649750925721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11536576626108264009874357 1081554058697649750925721)
                      ·
                        rfl

theorem cell23_2106319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_2106319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106319 prefixEnd_2106319 := by exact prefixLift 2106319
  have htrace : WordTrace (prefixWord ++ tailWord_2106319) baseStart_2106319 baseEnd_2106319 := by
    simpa [prefixWord, tailWord_2106319, baseEnd_2106319] using wordTrace_append hprefix tailTrace_2106319
  have hstable : (prefixWord ++ tailWord_2106319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106319).length < 2 ^ (prefixWord ++ tailWord_2106319).sum := by decide
  have hdescent : baseEnd_2106319 < baseStart_2106319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106343 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2106343 : Nat := 118140960795 + 2106343 * 2 ^ 59
def prefixEnd_2106343 : Nat := 4983230072969 + 3 ^ 40 * 2106343 * 2
def baseEnd_2106343 : Nat := 360522127411119219008537

theorem tailTrace_2106343 : CollatzResearch.WordTrace tailWord_2106343 prefixEnd_2106343 360522127411119219008537 := by
  unfold tailWord_2106343
  simp only [CollatzResearch.WordTrace]
  refine ⟨76824640608086520589563683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51216427072057680393042455 76824640608086520589563683)
  ·
    refine ⟨115236960912129780884345525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76824640608086520589563683 115236960912129780884345525)
    ·
      refine ⟨10803465085512166957907393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115236960912129780884345525 10803465085512166957907393)
      ·
        refine ⟨8102598814134125218430545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10803465085512166957907393 8102598814134125218430545)
        ·
          refine ⟨6076949110600593913822909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8102598814134125218430545 6076949110600593913822909)
          ·
            refine ⟨2278855916475222717683591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6076949110600593913822909 2278855916475222717683591)
            ·
              refine ⟨3418283874712834076525387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278855916475222717683591 3418283874712834076525387)
              ·
                refine ⟨5127425812069251114788081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418283874712834076525387 5127425812069251114788081)
                ·
                  refine ⟨3845569359051938336091061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5127425812069251114788081 3845569359051938336091061)
                  ·
                    refine ⟨360522127411119219008537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3845569359051938336091061 360522127411119219008537)
                    ·
                      rfl

theorem cell23_2106343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2106343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106343 prefixEnd_2106343 := by exact prefixLift 2106343
  have htrace : WordTrace (prefixWord ++ tailWord_2106343) baseStart_2106343 baseEnd_2106343 := by
    simpa [prefixWord, tailWord_2106343, baseEnd_2106343] using wordTrace_append hprefix tailTrace_2106343
  have hstable : (prefixWord ++ tailWord_2106343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106343).length < 2 ^ (prefixWord ++ tailWord_2106343).sum := by decide
  have hdescent : baseEnd_2106343 < baseStart_2106343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106346 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2106346 : Nat := 118140960795 + 2106346 * 2 ^ 59
def prefixEnd_2106346 : Nat := 4983230072969 + 3 ^ 40 * 2106346 * 2
def baseEnd_2106346 : Nat := 1081567922675321145288097

theorem tailTrace_2106346 : CollatzResearch.WordTrace tailWord_2106346 prefixEnd_2106346 1081567922675321145288097 := by
  unfold tailWord_2106346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19206187506768913025480723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51216500018050434734615261 19206187506768913025480723)
  ·
    refine ⟨28809281260153369538221085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19206187506768913025480723 28809281260153369538221085)
    ·
      refine ⟨10803480472557513576832907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28809281260153369538221085 10803480472557513576832907)
      ·
        refine ⟨16205220708836270365249361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10803480472557513576832907 16205220708836270365249361)
        ·
          refine ⟨12153915531627202773937021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16205220708836270365249361 12153915531627202773937021)
          ·
            refine ⟨4557718324360201040226383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12153915531627202773937021 4557718324360201040226383)
            ·
              refine ⟨6836577486540301560339575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557718324360201040226383 6836577486540301560339575)
              ·
                refine ⟨10254866229810452340509363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6836577486540301560339575 10254866229810452340509363)
                ·
                  refine ⟨15382299344715678510764045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10254866229810452340509363 15382299344715678510764045)
                  ·
                    refine ⟨5768362254268379441536517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15382299344715678510764045 5768362254268379441536517)
                    ·
                      refine ⟨1081567922675321145288097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5768362254268379441536517 1081567922675321145288097)
                      ·
                        rfl

theorem cell23_2106346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2106346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106346 prefixEnd_2106346 := by exact prefixLift 2106346
  have htrace : WordTrace (prefixWord ++ tailWord_2106346) baseStart_2106346 baseEnd_2106346 := by
    simpa [prefixWord, tailWord_2106346, baseEnd_2106346] using wordTrace_append hprefix tailTrace_2106346
  have hstable : (prefixWord ++ tailWord_2106346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106346).length < 2 ^ (prefixWord ++ tailWord_2106346).sum := by decide
  have hdescent : baseEnd_2106346 < baseStart_2106346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106373 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_2106373 : Nat := 118140960795 + 2106373 * 2 ^ 59
def prefixEnd_2106373 : Nat := 4983230072969 + 3 ^ 40 * 2106373 * 2
def baseEnd_2106373 : Nat := 360527262217664179883491

theorem tailTrace_2106373 : CollatzResearch.WordTrace tailWord_2106373 prefixEnd_2106373 360527262217664179883491 := by
  unfold tailWord_2106373
  simp only [CollatzResearch.WordTrace]
  refine ⟨76825734797977835713155773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51217156531985223808770515 76825734797977835713155773)
  ·
    refine ⟨28809650549241688392433415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76825734797977835713155773 28809650549241688392433415)
    ·
      refine ⟨43214475823862532588650123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28809650549241688392433415 43214475823862532588650123)
      ·
        refine ⟨64821713735793798882975185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43214475823862532588650123 64821713735793798882975185)
        ·
          refine ⟨48616285301845349162231389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64821713735793798882975185 48616285301845349162231389)
          ·
            refine ⟨18231106988192005935836771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48616285301845349162231389 18231106988192005935836771)
            ·
              refine ⟨27346660482288008903755157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18231106988192005935836771 27346660482288008903755157)
              ·
                refine ⟨1281874710107250417363523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27346660482288008903755157 1281874710107250417363523)
                ·
                  refine ⟨1922812065160875626045285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281874710107250417363523 1922812065160875626045285)
                  ·
                    refine ⟨360527262217664179883491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922812065160875626045285 360527262217664179883491)
                    ·
                      rfl

theorem cell23_2106373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_2106373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106373 prefixEnd_2106373 := by exact prefixLift 2106373
  have htrace : WordTrace (prefixWord ++ tailWord_2106373) baseStart_2106373 baseEnd_2106373 := by
    simpa [prefixWord, tailWord_2106373, baseEnd_2106373] using wordTrace_append hprefix tailTrace_2106373
  have hstable : (prefixWord ++ tailWord_2106373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106373).length < 2 ^ (prefixWord ++ tailWord_2106373).sum := by decide
  have hdescent : baseEnd_2106373 < baseStart_2106373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106407 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2106407 : Nat := 118140960795 + 2106407 * 2 ^ 59
def prefixEnd_2106407 : Nat := 4983230072969 + 3 ^ 40 * 2106407 * 2
def baseEnd_2106407 : Nat := 360533081665081802208439

theorem tailTrace_2106407 : CollatzResearch.WordTrace tailWord_2106407 prefixEnd_2106407 360533081665081802208439 := by
  unfold tailWord_2106407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76826974879854659519893475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51217983253236439679928983 76826974879854659519893475)
  ·
    refine ⟨115240462319781989279840213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76826974879854659519893475 115240462319781989279840213)
    ·
      refine ⟨2700948335619890373746255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 115240462319781989279840213 2700948335619890373746255)
      ·
        refine ⟨4051422503429835560619383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700948335619890373746255 4051422503429835560619383)
        ·
          refine ⟨6077133755144753340929075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051422503429835560619383 6077133755144753340929075)
          ·
            refine ⟨9115700632717130011393613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6077133755144753340929075 9115700632717130011393613)
            ·
              refine ⟨3418387737268923754272605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9115700632717130011393613 3418387737268923754272605)
              ·
                refine ⟨1281895401475846407852227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3418387737268923754272605 1281895401475846407852227)
                ·
                  refine ⟨1922843102213769611778341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281895401475846407852227 1922843102213769611778341)
                  ·
                    refine ⟨360533081665081802208439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922843102213769611778341 360533081665081802208439)
                    ·
                      rfl

theorem cell23_2106407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2106407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106407 prefixEnd_2106407 := by exact prefixLift 2106407
  have htrace : WordTrace (prefixWord ++ tailWord_2106407) baseStart_2106407 baseEnd_2106407 := by
    simpa [prefixWord, tailWord_2106407, baseEnd_2106407] using wordTrace_append hprefix tailTrace_2106407
  have hstable : (prefixWord ++ tailWord_2106407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106407).length < 2 ^ (prefixWord ++ tailWord_2106407).sum := by decide
  have hdescent : baseEnd_2106407 < baseStart_2106407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106416 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_2106416 : Nat := 118140960795 + 2106416 * 2 ^ 59
def prefixEnd_2106416 : Nat := 4983230072969 + 3 ^ 40 * 2106416 * 2
def baseEnd_2106416 : Nat := 360534622107045290470925

theorem tailTrace_2106416 : CollatzResearch.WordTrace tailWord_2106416 prefixEnd_2106416 360534622107045290470925 := by
  unfold tailWord_2106416
  simp only [CollatzResearch.WordTrace]
  refine ⟨38413651568411027028485551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51218202091214702704647401 38413651568411027028485551)
  ·
    refine ⟨57620477352616540542728327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38413651568411027028485551 57620477352616540542728327)
    ·
      refine ⟨86430716028924810814092491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57620477352616540542728327 86430716028924810814092491)
      ·
        refine ⟨129646074043387216221138737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86430716028924810814092491 129646074043387216221138737)
        ·
          refine ⟨97234555532540412165854053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129646074043387216221138737 97234555532540412165854053)
          ·
            refine ⟨18231479162351327281097635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97234555532540412165854053 18231479162351327281097635)
            ·
              refine ⟨27347218743526990921646453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18231479162351327281097635 27347218743526990921646453)
              ·
                refine ⟨2563801757205655398904355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27347218743526990921646453 2563801757205655398904355)
                ·
                  refine ⟨3845702635808483098356533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563801757205655398904355 3845702635808483098356533)
                  ·
                    refine ⟨360534622107045290470925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3845702635808483098356533 360534622107045290470925)
                    ·
                      rfl

theorem cell23_2106416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_2106416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106416 prefixEnd_2106416 := by exact prefixLift 2106416
  have htrace : WordTrace (prefixWord ++ tailWord_2106416) baseStart_2106416 baseEnd_2106416 := by
    simpa [prefixWord, tailWord_2106416, baseEnd_2106416] using wordTrace_append hprefix tailTrace_2106416
  have hstable : (prefixWord ++ tailWord_2106416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106416).length < 2 ^ (prefixWord ++ tailWord_2106416).sum := by decide
  have hdescent : baseEnd_2106416 < baseStart_2106416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106446 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2106446 : Nat := 118140960795 + 2106446 * 2 ^ 59
def prefixEnd_2106446 : Nat := 4983230072969 + 3 ^ 40 * 2106446 * 2
def baseEnd_2106446 : Nat := 360539756913590251345879

theorem tailTrace_2106446 : CollatzResearch.WordTrace tailWord_2106446 prefixEnd_2106446 360539756913590251345879 := by
  unfold tailWord_2106446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9603549665839171147570399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51218931551142246120375461 9603549665839171147570399)
  ·
    refine ⟨14405324498758756721355599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9603549665839171147570399 14405324498758756721355599)
    ·
      refine ⟨21607986748138135082033399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14405324498758756721355599 21607986748138135082033399)
      ·
        refine ⟨32411980122207202623050099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21607986748138135082033399 32411980122207202623050099)
        ·
          refine ⟨48617970183310803934575149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32411980122207202623050099 48617970183310803934575149)
          ·
            refine ⟨18231738818741551475465681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48617970183310803934575149 18231738818741551475465681)
            ·
              refine ⟨13673804114056163606599261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18231738818741551475465681 13673804114056163606599261)
              ·
                refine ⟨5127676542771061352474723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13673804114056163606599261 5127676542771061352474723)
                ·
                  refine ⟨7691514814156592028712085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5127676542771061352474723 7691514814156592028712085)
                  ·
                    refine ⟨360539756913590251345879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7691514814156592028712085 360539756913590251345879)
                    ·
                      rfl

theorem cell23_2106446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2106446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106446 prefixEnd_2106446 := by exact prefixLift 2106446
  have htrace : WordTrace (prefixWord ++ tailWord_2106446) baseStart_2106446 baseEnd_2106446 := by
    simpa [prefixWord, tailWord_2106446, baseEnd_2106446] using wordTrace_append hprefix tailTrace_2106446
  have hstable : (prefixWord ++ tailWord_2106446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106446).length < 2 ^ (prefixWord ++ tailWord_2106446).sum := by decide
  have hdescent : baseEnd_2106446 < baseStart_2106446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106450 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2106450 : Nat := 118140960795 + 2106450 * 2 ^ 59
def prefixEnd_2106450 : Nat := 4983230072969 + 3 ^ 40 * 2106450 * 2
def baseEnd_2106450 : Nat := 360540441554462912795873

theorem tailTrace_2106450 : CollatzResearch.WordTrace tailWord_2106450 prefixEnd_2106450 360540441554462912795873 := by
  unfold tailWord_2106450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19207135804674719465927201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51219028812465918575805869 19207135804674719465927201)
  ·
    refine ⟨14405351853506039599445401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19207135804674719465927201 14405351853506039599445401)
    ·
      refine ⟨10804013890129529699584051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14405351853506039599445401 10804013890129529699584051)
      ·
        refine ⟨16206020835194294549376077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10804013890129529699584051 16206020835194294549376077)
        ·
          refine ⟨6077257813197860456016029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16206020835194294549376077 6077257813197860456016029)
          ·
            refine ⟨2278971679949197671006011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6077257813197860456016029 2278971679949197671006011)
            ·
              refine ⟨3418457519923796506509017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278971679949197671006011 3418457519923796506509017)
              ·
                refine ⟨2563843139942847379881763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3418457519923796506509017 2563843139942847379881763)
                ·
                  refine ⟨3845764709914271069822645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563843139942847379881763 3845764709914271069822645)
                  ·
                    refine ⟨360540441554462912795873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3845764709914271069822645 360540441554462912795873)
                    ·
                      rfl

theorem cell23_2106450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2106450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106450 prefixEnd_2106450 := by exact prefixLift 2106450
  have htrace : WordTrace (prefixWord ++ tailWord_2106450) baseStart_2106450 baseEnd_2106450 := by
    simpa [prefixWord, tailWord_2106450, baseEnd_2106450] using wordTrace_append hprefix tailTrace_2106450
  have hstable : (prefixWord ++ tailWord_2106450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106450).length < 2 ^ (prefixWord ++ tailWord_2106450).sum := by decide
  have hdescent : baseEnd_2106450 < baseStart_2106450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106473 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_2106473 : Nat := 118140960795 + 2106473 * 2 ^ 59
def prefixEnd_2106473 : Nat := 4983230072969 + 3 ^ 40 * 2106473 * 2
def baseEnd_2106473 : Nat := 1081633134718442148400013

theorem tailTrace_2106473 : CollatzResearch.WordTrace tailWord_2106473 prefixEnd_2106473 1081633134718442148400013 := by
  unfold tailWord_2106473
  simp only [CollatzResearch.WordTrace]
  refine ⟨76829382097615552791796073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51219588065077035194530715 76829382097615552791796073)
  ·
    refine ⟨57622036573211664593847055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76829382097615552791796073 57622036573211664593847055)
    ·
      refine ⟨86433054859817496890770583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57622036573211664593847055 86433054859817496890770583)
      ·
        refine ⟨129649582289726245336155875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86433054859817496890770583 129649582289726245336155875)
        ·
          refine ⟨194474373434589368004233813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129649582289726245336155875 194474373434589368004233813)
          ·
            refine ⟨2278996563686594156299615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 194474373434589368004233813 2278996563686594156299615)
            ·
              refine ⟨3418494845529891234449423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278996563686594156299615 3418494845529891234449423)
              ·
                refine ⟨5127742268294836851674135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418494845529891234449423 5127742268294836851674135)
                ·
                  refine ⟨7691613402442255277511203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5127742268294836851674135 7691613402442255277511203)
                  ·
                    refine ⟨11537420103663382916266805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7691613402442255277511203 11537420103663382916266805)
                    ·
                      refine ⟨1081633134718442148400013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11537420103663382916266805 1081633134718442148400013)
                      ·
                        rfl

theorem cell23_2106473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_2106473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106473 prefixEnd_2106473 := by exact prefixLift 2106473
  have htrace : WordTrace (prefixWord ++ tailWord_2106473) baseStart_2106473 baseEnd_2106473 := by
    simpa [prefixWord, tailWord_2106473, baseEnd_2106473] using wordTrace_append hprefix tailTrace_2106473
  have hstable : (prefixWord ++ tailWord_2106473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106473).length < 2 ^ (prefixWord ++ tailWord_2106473).sum := by decide
  have hdescent : baseEnd_2106473 < baseStart_2106473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106487 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 1, 2, 2]
def baseStart_2106487 : Nat := 118140960795 + 2106487 * 2 ^ 59
def prefixEnd_2106487 : Nat := 4983230072969 + 3 ^ 40 * 2106487 * 2
def baseEnd_2106487 : Nat := 1081640323447605093624949

theorem tailTrace_2106487 : CollatzResearch.WordTrace tailWord_2106487 prefixEnd_2106487 1081640323447605093624949 := by
  unfold tailWord_2106487
  simp only [CollatzResearch.WordTrace]
  refine ⟨76829892719564833182805715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51219928479709888788537143 76829892719564833182805715)
  ·
    refine ⟨115244839079347249774208573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76829892719564833182805715 115244839079347249774208573)
    ·
      refine ⟨43216814654755218665328215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115244839079347249774208573 43216814654755218665328215)
      ·
        refine ⟨64825221982132827997992323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43216814654755218665328215 64825221982132827997992323)
        ·
          refine ⟨97237832973199241996988485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64825221982132827997992323 97237832973199241996988485)
          ·
            refine ⟨18232093682474857874435341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97237832973199241996988485 18232093682474857874435341)
            ·
              refine ⟨6837035130928071702913253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18232093682474857874435341 6837035130928071702913253)
              ·
                refine ⟨1281944087049013444296235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6837035130928071702913253 1281944087049013444296235)
                ·
                  refine ⟨1922916130573520166444353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281944087049013444296235 1922916130573520166444353)
                  ·
                    refine ⟨1442187097930140124833265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1922916130573520166444353 1442187097930140124833265)
                    ·
                      refine ⟨1081640323447605093624949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442187097930140124833265 1081640323447605093624949)
                      ·
                        rfl

theorem cell23_2106487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_2106487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106487 prefixEnd_2106487 := by exact prefixLift 2106487
  have htrace : WordTrace (prefixWord ++ tailWord_2106487) baseStart_2106487 baseEnd_2106487 := by
    simpa [prefixWord, tailWord_2106487, baseEnd_2106487] using wordTrace_append hprefix tailTrace_2106487
  have hstable : (prefixWord ++ tailWord_2106487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106487).length < 2 ^ (prefixWord ++ tailWord_2106487).sum := by decide
  have hdescent : baseEnd_2106487 < baseStart_2106487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106503 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_2106503 : Nat := 118140960795 + 2106503 * 2 ^ 59
def prefixEnd_2106503 : Nat := 4983230072969 + 3 ^ 40 * 2106503 * 2
def baseEnd_2106503 : Nat := 1081648539138077031024875

theorem tailTrace_2106503 : CollatzResearch.WordTrace tailWord_2106503 prefixEnd_2106503 1081648539138077031024875 := by
  unfold tailWord_2106503
  simp only [CollatzResearch.WordTrace]
  refine ⟨76830476287506867915388163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51220317525004578610258775 76830476287506867915388163)
  ·
    refine ⟨115245714431260301873082245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76830476287506867915388163 115245714431260301873082245)
    ·
      refine ⟨21608571455861306601202921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115245714431260301873082245 21608571455861306601202921)
      ·
        refine ⟨16206428591895979950902191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21608571455861306601202921 16206428591895979950902191)
        ·
          refine ⟨24309642887843969926353287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16206428591895979950902191 24309642887843969926353287)
          ·
            refine ⟨36464464331765954889529931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24309642887843969926353287 36464464331765954889529931)
            ·
              refine ⟨54696696497648932334294897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36464464331765954889529931 54696696497648932334294897)
              ·
                refine ⟨41022522373236699250721173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54696696497648932334294897 41022522373236699250721173)
                ·
                  refine ⟨1922930736245470277377555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41022522373236699250721173 1922930736245470277377555)
                  ·
                    refine ⟨2884396104368205416066333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922930736245470277377555 2884396104368205416066333)
                    ·
                      refine ⟨1081648539138077031024875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2884396104368205416066333 1081648539138077031024875)
                      ·
                        rfl

theorem cell23_2106503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_2106503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106503 prefixEnd_2106503 := by exact prefixLift 2106503
  have htrace : WordTrace (prefixWord ++ tailWord_2106503) baseStart_2106503 baseEnd_2106503 := by
    simpa [prefixWord, tailWord_2106503, baseEnd_2106503] using wordTrace_append hprefix tailTrace_2106503
  have hstable : (prefixWord ++ tailWord_2106503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106503).length < 2 ^ (prefixWord ++ tailWord_2106503).sum := by decide
  have hdescent : baseEnd_2106503 < baseStart_2106503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106506 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_2106506 : Nat := 118140960795 + 2106506 * 2 ^ 59
def prefixEnd_2106506 : Nat := 4983230072969 + 3 ^ 40 * 2106506 * 2
def baseEnd_2106506 : Nat := 360550026526680173095787

theorem tailTrace_2106506 : CollatzResearch.WordTrace tailWord_2106506 prefixEnd_2106506 360550026526680173095787 := by
  unfold tailWord_2106506
  simp only [CollatzResearch.WordTrace]
  refine ⟨19207646426623999856936843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51220390470997332951831581 19207646426623999856936843)
  ·
    refine ⟨28811469639935999785405265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19207646426623999856936843 28811469639935999785405265)
    ·
      refine ⟨21608602229951999839053949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28811469639935999785405265 21608602229951999839053949)
      ·
        refine ⟨8103225836231999939645231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21608602229951999839053949 8103225836231999939645231)
        ·
          refine ⟨12154838754347999909467847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103225836231999939645231 12154838754347999909467847)
          ·
            refine ⟨18232258131521999864201771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12154838754347999909467847 18232258131521999864201771)
            ·
              refine ⟨27348387197282999796302657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18232258131521999864201771 27348387197282999796302657)
              ·
                refine ⟨20511290397962249847226993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27348387197282999796302657 20511290397962249847226993)
                ·
                  refine ⟨15383467798471687385420245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20511290397962249847226993 15383467798471687385420245)
                  ·
                    refine ⟨360550026526680173095787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15383467798471687385420245 360550026526680173095787)
                    ·
                      rfl

theorem cell23_2106506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_2106506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106506 prefixEnd_2106506 := by exact prefixLift 2106506
  have htrace : WordTrace (prefixWord ++ tailWord_2106506) baseStart_2106506 baseEnd_2106506 := by
    simpa [prefixWord, tailWord_2106506, baseEnd_2106506] using wordTrace_append hprefix tailTrace_2106506
  have hstable : (prefixWord ++ tailWord_2106506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106506).length < 2 ^ (prefixWord ++ tailWord_2106506).sum := by decide
  have hdescent : baseEnd_2106506 < baseStart_2106506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106543 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 3, 4, 2]
def baseStart_2106543 : Nat := 118140960795 + 2106543 * 2 ^ 59
def prefixEnd_2106543 : Nat := 4983230072969 + 3 ^ 40 * 2106543 * 2
def baseEnd_2106543 : Nat := 1081669078364256874524691

theorem tailTrace_2106543 : CollatzResearch.WordTrace tailWord_2106543 prefixEnd_2106543 1081669078364256874524691 := by
  unfold tailWord_2106543
  simp only [CollatzResearch.WordTrace]
  refine ⟨76831935207361954746844283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51221290138241303164562855 76831935207361954746844283)
  ·
    refine ⟨115247902811042932120266425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76831935207361954746844283 115247902811042932120266425)
    ·
      refine ⟨86435927108282199090199819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115247902811042932120266425 86435927108282199090199819)
      ·
        refine ⟨129653890662423298635299729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86435927108282199090199819 129653890662423298635299729)
        ·
          refine ⟨97240417996817473976474797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129653890662423298635299729 97240417996817473976474797)
          ·
            refine ⟨36465156748806552741178049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97240417996817473976474797 36465156748806552741178049)
            ·
              refine ⟨27348867561604914555883537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36465156748806552741178049 27348867561604914555883537)
              ·
                refine ⟨20511650671203685916912653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27348867561604914555883537 20511650671203685916912653)
                ·
                  refine ⟨7691869001701382218842245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20511650671203685916912653 7691869001701382218842245)
                  ·
                    refine ⟨1442225437819009166032921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7691869001701382218842245 1442225437819009166032921)
                    ·
                      refine ⟨1081669078364256874524691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442225437819009166032921 1081669078364256874524691)
                      ·
                        rfl

theorem cell23_2106543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4, 2].length) (baseStart_2106543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106543 prefixEnd_2106543 := by exact prefixLift 2106543
  have htrace : WordTrace (prefixWord ++ tailWord_2106543) baseStart_2106543 baseEnd_2106543 := by
    simpa [prefixWord, tailWord_2106543, baseEnd_2106543] using wordTrace_append hprefix tailTrace_2106543
  have hstable : (prefixWord ++ tailWord_2106543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106543).length < 2 ^ (prefixWord ++ tailWord_2106543).sum := by decide
  have hdescent : baseEnd_2106543 < baseStart_2106543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106564 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2106564 : Nat := 118140960795 + 2106564 * 2 ^ 59
def prefixEnd_2106564 : Nat := 4983230072969 + 3 ^ 40 * 2106564 * 2
def baseEnd_2106564 : Nat := 1081679861458001292362095

theorem tailTrace_2106564 : CollatzResearch.WordTrace tailWord_2106564 prefixEnd_2106564 1081679861458001292362095 := by
  unfold tailWord_2106564
  simp only [CollatzResearch.WordTrace]
  refine ⟨38416350570142937666679373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51221800760190583555572497 38416350570142937666679373)
  ·
    refine ⟨14406131463803601625004765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38416350570142937666679373 14406131463803601625004765)
    ·
      refine ⟨5402299298926350609376787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14406131463803601625004765 5402299298926350609376787)
      ·
        refine ⟨8103448948389525914065181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402299298926350609376787 8103448948389525914065181)
        ·
          refine ⟨3038793355646072217774443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8103448948389525914065181 3038793355646072217774443)
          ·
            refine ⟨4558190033469108326661665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038793355646072217774443 4558190033469108326661665)
            ·
              refine ⟨3418642525101831244996249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4558190033469108326661665 3418642525101831244996249)
              ·
                refine ⟨2563981893826373433747187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3418642525101831244996249 2563981893826373433747187)
                ·
                  refine ⟨3845972840739560150620781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563981893826373433747187 3845972840739560150620781)
                  ·
                    refine ⟨1442239815277335056482793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3845972840739560150620781 1442239815277335056482793)
                    ·
                      refine ⟨1081679861458001292362095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442239815277335056482793 1081679861458001292362095)
                      ·
                        rfl

theorem cell23_2106564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2106564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106564 prefixEnd_2106564 := by exact prefixLift 2106564
  have htrace : WordTrace (prefixWord ++ tailWord_2106564) baseStart_2106564 baseEnd_2106564 := by
    simpa [prefixWord, tailWord_2106564, baseEnd_2106564] using wordTrace_append hprefix tailTrace_2106564
  have hstable : (prefixWord ++ tailWord_2106564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106564).length < 2 ^ (prefixWord ++ tailWord_2106564).sum := by decide
  have hdescent : baseEnd_2106564 < baseStart_2106564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106650 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_2106650 : Nat := 118140960795 + 2106650 * 2 ^ 59
def prefixEnd_2106650 : Nat := 4983230072969 + 3 ^ 40 * 2106650 * 2
def baseEnd_2106650 : Nat := 1081724020794287955886699

theorem tailTrace_2106650 : CollatzResearch.WordTrace tailWord_2106650 prefixEnd_2106650 1081724020794287955886699 := by
  unfold tailWord_2106650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19208959454493578005247351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51223891878649541347326269 19208959454493578005247351)
  ·
    refine ⟨28813439181740367007871027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19208959454493578005247351 28813439181740367007871027)
    ·
      refine ⟨43220158772610550511806541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28813439181740367007871027 43220158772610550511806541)
      ·
        refine ⟨16207559539728956441927453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43220158772610550511806541 16207559539728956441927453)
        ·
          refine ⟨6077834827398358665722795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16207559539728956441927453 6077834827398358665722795)
          ·
            refine ⟨9116752241097537998584193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6077834827398358665722795 9116752241097537998584193)
            ·
              refine ⟨6837564180823153498938145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9116752241097537998584193 6837564180823153498938145)
              ·
                refine ⟨5128173135617365124203609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6837564180823153498938145 5128173135617365124203609)
                ·
                  refine ⟨3846129851713023843152707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5128173135617365124203609 3846129851713023843152707)
                  ·
                    refine ⟨5769194777569535764729061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3846129851713023843152707 5769194777569535764729061)
                    ·
                      refine ⟨1081724020794287955886699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5769194777569535764729061 1081724020794287955886699)
                      ·
                        rfl

theorem cell23_2106650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_2106650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106650 prefixEnd_2106650 := by exact prefixLift 2106650
  have htrace : WordTrace (prefixWord ++ tailWord_2106650) baseStart_2106650 baseEnd_2106650 := by
    simpa [prefixWord, tailWord_2106650, baseEnd_2106650] using wordTrace_append hprefix tailTrace_2106650
  have hstable : (prefixWord ++ tailWord_2106650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106650).length < 2 ^ (prefixWord ++ tailWord_2106650).sum := by decide
  have hdescent : baseEnd_2106650 < baseStart_2106650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106660 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_2106660 : Nat := 118140960795 + 2106660 * 2 ^ 59
def prefixEnd_2106660 : Nat := 4983230072969 + 3 ^ 40 * 2106660 * 2
def baseEnd_2106660 : Nat := 360576385200277638920551

theorem tailTrace_2106660 : CollatzResearch.WordTrace tailWord_2106660 prefixEnd_2106660 360576385200277638920551 := by
  unfold tailWord_2106660
  simp only [CollatzResearch.WordTrace]
  refine ⟨38418101273969041864426717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51224135031958722485902289 38418101273969041864426717)
  ·
    refine ⟨14406787977738390699160019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38418101273969041864426717 14406787977738390699160019)
    ·
      refine ⟨21610181966607586048740029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14406787977738390699160019 21610181966607586048740029)
      ·
        refine ⟨8103818237477844768277511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21610181966607586048740029 8103818237477844768277511)
        ·
          refine ⟨12155727356216767152416267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103818237477844768277511 12155727356216767152416267)
          ·
            refine ⟨18233591034325150728624401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12155727356216767152416267 18233591034325150728624401)
            ·
              refine ⟨13675193275743863046468301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18233591034325150728624401 13675193275743863046468301)
              ·
                refine ⟨5128197478403948642425613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13675193275743863046468301 5128197478403948642425613)
                ·
                  refine ⟨1923074054401480740909605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5128197478403948642425613 1923074054401480740909605)
                  ·
                    refine ⟨360576385200277638920551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923074054401480740909605 360576385200277638920551)
                    ·
                      rfl

theorem cell23_2106660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_2106660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106660 prefixEnd_2106660 := by exact prefixLift 2106660
  have htrace : WordTrace (prefixWord ++ tailWord_2106660) baseStart_2106660 baseEnd_2106660 := by
    simpa [prefixWord, tailWord_2106660, baseEnd_2106660] using wordTrace_append hprefix tailTrace_2106660
  have hstable : (prefixWord ++ tailWord_2106660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106660).length < 2 ^ (prefixWord ++ tailWord_2106660).sum := by decide
  have hdescent : baseEnd_2106660 < baseStart_2106660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106687 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_2106687 : Nat := 118140960795 + 2106687 * 2 ^ 59
def prefixEnd_2106687 : Nat := 4983230072969 + 3 ^ 40 * 2106687 * 2
def baseEnd_2106687 : Nat := 1081743019578504311124029

theorem tailTrace_2106687 : CollatzResearch.WordTrace tailWord_2106687 prefixEnd_2106687 1081743019578504311124029 := by
  unfold tailWord_2106687
  simp only [CollatzResearch.WordTrace]
  refine ⟨76837187318840267340086315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51224791545893511560057543 76837187318840267340086315)
  ·
    refine ⟨115255780978260401010129473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76837187318840267340086315 115255780978260401010129473)
    ·
      refine ⟨86441835733695300757597105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115255780978260401010129473 86441835733695300757597105)
      ·
        refine ⟨64831376800271475568197829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86441835733695300757597105 64831376800271475568197829)
        ·
          refine ⟨12155883150050901669037093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64831376800271475568197829 12155883150050901669037093)
          ·
            refine ⟨2279228090634544062944455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12155883150050901669037093 2279228090634544062944455)
            ·
              refine ⟨3418842135951816094416683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279228090634544062944455 3418842135951816094416683)
              ·
                refine ⟨5128263203927724141625025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418842135951816094416683 5128263203927724141625025)
                ·
                  refine ⟨3846197402945793106218769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5128263203927724141625025 3846197402945793106218769)
                  ·
                    refine ⟨2884648052209344829664077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3846197402945793106218769 2884648052209344829664077)
                    ·
                      refine ⟨1081743019578504311124029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2884648052209344829664077 1081743019578504311124029)
                      ·
                        rfl

theorem cell23_2106687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_2106687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106687 prefixEnd_2106687 := by exact prefixLift 2106687
  have htrace : WordTrace (prefixWord ++ tailWord_2106687) baseStart_2106687 baseEnd_2106687 := by
    simpa [prefixWord, tailWord_2106687, baseEnd_2106687] using wordTrace_append hprefix tailTrace_2106687
  have hstable : (prefixWord ++ tailWord_2106687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106687).length < 2 ^ (prefixWord ++ tailWord_2106687).sum := by decide
  have hdescent : baseEnd_2106687 < baseStart_2106687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106743 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_2106743 : Nat := 118140960795 + 2106743 * 2 ^ 59
def prefixEnd_2106743 : Nat := 4983230072969 + 3 ^ 40 * 2106743 * 2
def baseEnd_2106743 : Nat := 1081771774495156092023771

theorem tailTrace_2106743 : CollatzResearch.WordTrace tailWord_2106743 prefixEnd_2106743 1081771774495156092023771 := by
  unfold tailWord_2106743
  simp only [CollatzResearch.WordTrace]
  refine ⟨76839229806637388904124883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51226153204424925936083255 76839229806637388904124883)
  ·
    refine ⟨115258844709956083356187325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76839229806637388904124883 115258844709956083356187325)
    ·
      refine ⟨43222066766233531258570247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115258844709956083356187325 43222066766233531258570247)
      ·
        refine ⟨64833100149350296887855371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43222066766233531258570247 64833100149350296887855371)
        ·
          refine ⟨97249650224025445331783057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64833100149350296887855371 97249650224025445331783057)
          ·
            refine ⟨72937237668019083998837293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97249650224025445331783057 72937237668019083998837293)
            ·
              refine ⟨27351464125507156499563985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72937237668019083998837293 27351464125507156499563985)
              ·
                refine ⟨20513598094130367374672989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27351464125507156499563985 20513598094130367374672989)
                ·
                  refine ⟨7692599285298887765502371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20513598094130367374672989 7692599285298887765502371)
                  ·
                    refine ⟨11538898927948331648253557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7692599285298887765502371 11538898927948331648253557)
                    ·
                      refine ⟨1081771774495156092023771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11538898927948331648253557 1081771774495156092023771)
                      ·
                        rfl

theorem cell23_2106743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_2106743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106743 prefixEnd_2106743 := by exact prefixLift 2106743
  have htrace : WordTrace (prefixWord ++ tailWord_2106743) baseStart_2106743 baseEnd_2106743 := by
    simpa [prefixWord, tailWord_2106743, baseEnd_2106743] using wordTrace_append hprefix tailTrace_2106743
  have hstable : (prefixWord ++ tailWord_2106743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106743).length < 2 ^ (prefixWord ++ tailWord_2106743).sum := by decide
  have hdescent : baseEnd_2106743 < baseStart_2106743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106754 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2106754 : Nat := 118140960795 + 2106754 * 2 ^ 59
def prefixEnd_2106754 : Nat := 4983230072969 + 3 ^ 40 * 2106754 * 2
def baseEnd_2106754 : Nat := 360592474260785182995407

theorem tailTrace_2106754 : CollatzResearch.WordTrace tailWord_2106754 prefixEnd_2106754 360592474260785182995407 := by
  unfold tailWord_2106754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19209907752399384445693829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51226420673065025188516877 19209907752399384445693829)
  ·
    refine ⟨3601857703574884583567593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19209907752399384445693829 3601857703574884583567593)
    ·
      refine ⟨2701393277681163437675695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3601857703574884583567593 2701393277681163437675695)
      ·
        refine ⟨4052089916521745156513543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701393277681163437675695 4052089916521745156513543)
        ·
          refine ⟨6078134874782617734770315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052089916521745156513543 6078134874782617734770315)
          ·
            refine ⟨9117202312173926602155473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078134874782617734770315 9117202312173926602155473)
            ·
              refine ⟨6837901734130444951616605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9117202312173926602155473 6837901734130444951616605)
              ·
                refine ⟨2564213150298916856856227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6837901734130444951616605 2564213150298916856856227)
                ·
                  refine ⟨3846319725448375285284341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564213150298916856856227 3846319725448375285284341)
                  ·
                    refine ⟨360592474260785182995407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3846319725448375285284341 360592474260785182995407)
                    ·
                      rfl

theorem cell23_2106754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2106754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106754 prefixEnd_2106754 := by exact prefixLift 2106754
  have htrace : WordTrace (prefixWord ++ tailWord_2106754) baseStart_2106754 baseEnd_2106754 := by
    simpa [prefixWord, tailWord_2106754, baseEnd_2106754] using wordTrace_append hprefix tailTrace_2106754
  have hstable : (prefixWord ++ tailWord_2106754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106754).length < 2 ^ (prefixWord ++ tailWord_2106754).sum := by decide
  have hdescent : baseEnd_2106754 < baseStart_2106754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106757 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_2106757 : Nat := 118140960795 + 2106757 * 2 ^ 59
def prefixEnd_2106757 : Nat := 4983230072969 + 3 ^ 40 * 2106757 * 2
def baseEnd_2106757 : Nat := 1081778963224319037248707

theorem tailTrace_2106757 : CollatzResearch.WordTrace tailWord_2106757 prefixEnd_2106757 1081778963224319037248707 := by
  unfold tailWord_2106757
  simp only [CollatzResearch.WordTrace]
  refine ⟨76839740428586669295134525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51226493619057779530089683 76839740428586669295134525)
  ·
    refine ⟨28814902660720000985675447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76839740428586669295134525 28814902660720000985675447)
    ·
      refine ⟨43222353991080001478513171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28814902660720000985675447 43222353991080001478513171)
      ·
        refine ⟨64833530986620002217769757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43222353991080001478513171 64833530986620002217769757)
        ·
          refine ⟨24312574119982500831663659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64833530986620002217769757 24312574119982500831663659)
          ·
            refine ⟨36468861179973751247495489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24312574119982500831663659 36468861179973751247495489)
            ·
              refine ⟨27351645884980313435621617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36468861179973751247495489 27351645884980313435621617)
              ·
                refine ⟨20513734413735235076716213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27351645884980313435621617 20513734413735235076716213)
                ·
                  refine ⟨1923162601287678288442145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20513734413735235076716213 1923162601287678288442145)
                  ·
                    refine ⟨1442371950965758716331609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923162601287678288442145 1442371950965758716331609)
                    ·
                      refine ⟨1081778963224319037248707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442371950965758716331609 1081778963224319037248707)
                      ·
                        rfl

theorem cell23_2106757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_2106757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106757 prefixEnd_2106757 := by exact prefixLift 2106757
  have htrace : WordTrace (prefixWord ++ tailWord_2106757) baseStart_2106757 baseEnd_2106757 := by
    simpa [prefixWord, tailWord_2106757, baseEnd_2106757] using wordTrace_append hprefix tailTrace_2106757
  have hstable : (prefixWord ++ tailWord_2106757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106757).length < 2 ^ (prefixWord ++ tailWord_2106757).sum := by decide
  have hdescent : baseEnd_2106757 < baseStart_2106757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106760 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2106760 : Nat := 118140960795 + 2106760 * 2 ^ 59
def prefixEnd_2106760 : Nat := 4983230072969 + 3 ^ 40 * 2106760 * 2
def baseEnd_2106760 : Nat := 1081780503666282525511193

theorem tailTrace_2106760 : CollatzResearch.WordTrace tailWord_2106760 prefixEnd_2106760 1081780503666282525511193 := by
  unfold tailWord_2106760
  simp only [CollatzResearch.WordTrace]
  refine ⟨38419924923787900403746867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51226566565050533871662489 38419924923787900403746867)
  ·
    refine ⟨57629887385681850605620301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38419924923787900403746867 57629887385681850605620301)
    ·
      refine ⟨21611207769630693977107613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57629887385681850605620301 21611207769630693977107613)
      ·
        refine ⟨8104202913611510241415355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21611207769630693977107613 8104202913611510241415355)
        ·
          refine ⟨12156304370417265362123033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104202913611510241415355 12156304370417265362123033)
          ·
            refine ⟨9117228277812949021592275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12156304370417265362123033 9117228277812949021592275)
            ·
              refine ⟨13675842416719423532388413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9117228277812949021592275 13675842416719423532388413)
              ·
                refine ⟨5128440906269783824645655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13675842416719423532388413 5128440906269783824645655)
                ·
                  refine ⟨7692661359404675736968483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128440906269783824645655 7692661359404675736968483)
                  ·
                    refine ⟨11538992039107013605452725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7692661359404675736968483 11538992039107013605452725)
                    ·
                      refine ⟨1081780503666282525511193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11538992039107013605452725 1081780503666282525511193)
                      ·
                        rfl

theorem cell23_2106760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2106760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106760 prefixEnd_2106760 := by exact prefixLift 2106760
  have htrace : WordTrace (prefixWord ++ tailWord_2106760) baseStart_2106760 baseEnd_2106760 := by
    simpa [prefixWord, tailWord_2106760, baseEnd_2106760] using wordTrace_append hprefix tailTrace_2106760
  have hstable : (prefixWord ++ tailWord_2106760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106760).length < 2 ^ (prefixWord ++ tailWord_2106760).sum := by decide
  have hdescent : baseEnd_2106760 < baseStart_2106760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106803 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_2106803 : Nat := 118140960795 + 2106803 * 2 ^ 59
def prefixEnd_2106803 : Nat := 4983230072969 + 3 ^ 40 * 2106803 * 2
def baseEnd_2106803 : Nat := 1081802583334425857273495

theorem tailTrace_2106803 : CollatzResearch.WordTrace tailWord_2106803 prefixEnd_2106803 1081802583334425857273495 := by
  unfold tailWord_2106803
  simp only [CollatzResearch.WordTrace]
  refine ⟨76841418186420019151309063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51227612124280012767539375 76841418186420019151309063)
  ·
    refine ⟨115262127279630028726963595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76841418186420019151309063 115262127279630028726963595)
    ·
      refine ⟨172893190919445043090445393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115262127279630028726963595 172893190919445043090445393)
      ·
        refine ⟨129669893189583782317834045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172893190919445043090445393 129669893189583782317834045)
        ·
          refine ⟨48626209946093918369187767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129669893189583782317834045 48626209946093918369187767)
          ·
            refine ⟨72939314919140877553781651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48626209946093918369187767 72939314919140877553781651)
            ·
              refine ⟨109408972378711316330672477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72939314919140877553781651 109408972378711316330672477)
              ·
                refine ⟨41028364642016743624002179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109408972378711316330672477 41028364642016743624002179)
                ·
                  refine ⟨61542546963025115436003269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41028364642016743624002179 61542546963025115436003269)
                  ·
                    refine ⟨11539227555567209144250613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61542546963025115436003269 11539227555567209144250613)
                    ·
                      refine ⟨1081802583334425857273495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11539227555567209144250613 1081802583334425857273495)
                      ·
                        rfl

theorem cell23_2106803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_2106803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106803 prefixEnd_2106803 := by exact prefixLift 2106803
  have htrace : WordTrace (prefixWord ++ tailWord_2106803) baseStart_2106803 baseEnd_2106803 := by
    simpa [prefixWord, tailWord_2106803, baseEnd_2106803] using wordTrace_append hprefix tailTrace_2106803
  have hstable : (prefixWord ++ tailWord_2106803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106803).length < 2 ^ (prefixWord ++ tailWord_2106803).sum := by decide
  have hdescent : baseEnd_2106803 < baseStart_2106803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106824 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_2106824 : Nat := 118140960795 + 2106824 * 2 ^ 59
def prefixEnd_2106824 : Nat := 4983230072969 + 3 ^ 40 * 2106824 * 2
def baseEnd_2106824 : Nat := 1081813366428170275110899

theorem tailTrace_2106824 : CollatzResearch.WordTrace tailWord_2106824 prefixEnd_2106824 1081813366428170275110899 := by
  unfold tailWord_2106824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38421092059671969868911763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51228122746229293158549017 38421092059671969868911763)
  ·
    refine ⟨57631638089507954803367645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38421092059671969868911763 57631638089507954803367645)
    ·
      refine ⟨21611864283565483051262867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57631638089507954803367645 21611864283565483051262867)
      ·
        refine ⟨32417796425348224576894301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21611864283565483051262867 32417796425348224576894301)
        ·
          refine ⟨12156673659505584216335363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32417796425348224576894301 12156673659505584216335363)
          ·
            refine ⟨18235010489258376324503045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12156673659505584216335363 18235010489258376324503045)
            ·
              refine ⟨3419064466735945560844321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18235010489258376324503045 3419064466735945560844321)
              ·
                refine ⟨2564298350051959170633241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419064466735945560844321 2564298350051959170633241)
                ·
                  refine ⟨1923223762538969377974931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2564298350051959170633241 1923223762538969377974931)
                  ·
                    refine ⟨2884835643808454066962397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1923223762538969377974931 2884835643808454066962397)
                    ·
                      refine ⟨1081813366428170275110899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2884835643808454066962397 1081813366428170275110899)
                      ·
                        rfl

theorem cell23_2106824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_2106824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106824 prefixEnd_2106824 := by exact prefixLift 2106824
  have htrace : WordTrace (prefixWord ++ tailWord_2106824) baseStart_2106824 baseEnd_2106824 := by
    simpa [prefixWord, tailWord_2106824, baseEnd_2106824] using wordTrace_append hprefix tailTrace_2106824
  have hstable : (prefixWord ++ tailWord_2106824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106824).length < 2 ^ (prefixWord ++ tailWord_2106824).sum := by decide
  have hdescent : baseEnd_2106824 < baseStart_2106824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106830 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2106830 : Nat := 118140960795 + 2106830 * 2 ^ 59
def prefixEnd_2106830 : Nat := 4983230072969 + 3 ^ 40 * 2106830 * 2
def baseEnd_2106830 : Nat := 1081816447312097251635871

theorem tailTrace_2106830 : CollatzResearch.WordTrace tailWord_2106830 prefixEnd_2106830 1081816447312097251635871 := by
  unfold tailWord_2106830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605300369665275345317743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51228268638214801841694629 9605300369665275345317743)
  ·
    refine ⟨14407950554497913017976615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9605300369665275345317743 14407950554497913017976615)
    ·
      refine ⟨21611925831746869526964923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14407950554497913017976615 21611925831746869526964923)
      ·
        refine ⟨32417888747620304290447385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21611925831746869526964923 32417888747620304290447385)
        ·
          refine ⟨24313416560715228217835539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32417888747620304290447385 24313416560715228217835539)
          ·
            refine ⟨36470124841072842326753309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24313416560715228217835539 36470124841072842326753309)
            ·
              refine ⟨13676296815402315872532491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36470124841072842326753309 13676296815402315872532491)
              ·
                refine ⟨20514445223103473808798737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13676296815402315872532491 20514445223103473808798737)
                ·
                  refine ⟨15385833917327605356599053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20514445223103473808798737 15385833917327605356599053)
                  ·
                    refine ⟨5769687718997852008724645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15385833917327605356599053 5769687718997852008724645)
                    ·
                      refine ⟨1081816447312097251635871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5769687718997852008724645 1081816447312097251635871)
                      ·
                        rfl

theorem cell23_2106830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2106830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106830 prefixEnd_2106830 := by exact prefixLift 2106830
  have htrace : WordTrace (prefixWord ++ tailWord_2106830) baseStart_2106830 baseEnd_2106830 := by
    simpa [prefixWord, tailWord_2106830, baseEnd_2106830] using wordTrace_append hprefix tailTrace_2106830
  have hstable : (prefixWord ++ tailWord_2106830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106830).length < 2 ^ (prefixWord ++ tailWord_2106830).sum := by decide
  have hdescent : baseEnd_2106830 < baseStart_2106830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106843 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_2106843 : Nat := 118140960795 + 2106843 * 2 ^ 59
def prefixEnd_2106843 : Nat := 4983230072969 + 3 ^ 40 * 2106843 * 2
def baseEnd_2106843 : Nat := 1081823122560605700773311

theorem tailTrace_2106843 : CollatzResearch.WordTrace tailWord_2106843 prefixEnd_2106843 1081823122560605700773311 := by
  unfold tailWord_2106843
  simp only [CollatzResearch.WordTrace]
  refine ⟨76842877106275105982765183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51228584737516737321843455 76842877106275105982765183)
  ·
    refine ⟨115264315659412658974147775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76842877106275105982765183 115264315659412658974147775)
    ·
      refine ⟨172896473489118988461221663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115264315659412658974147775 172896473489118988461221663)
      ·
        refine ⟨259344710233678482691832495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172896473489118988461221663 259344710233678482691832495)
        ·
          refine ⟨389017065350517724037748743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259344710233678482691832495 389017065350517724037748743)
          ·
            refine ⟨583525598025776586056623115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389017065350517724037748743 583525598025776586056623115)
            ·
              refine ⟨875288397038664879084934673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583525598025776586056623115 875288397038664879084934673)
              ·
                refine ⟨656466297778998659313701005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875288397038664879084934673 656466297778998659313701005)
                ·
                  refine ⟨246174861667124497242637877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656466297778998659313701005 246174861667124497242637877)
                  ·
                    refine ⟨23078893281292921616497301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 246174861667124497242637877 23078893281292921616497301)
                    ·
                      refine ⟨1081823122560605700773311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23078893281292921616497301 1081823122560605700773311)
                      ·
                        rfl

theorem cell23_2106843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_2106843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106843 prefixEnd_2106843 := by exact prefixLift 2106843
  have htrace : WordTrace (prefixWord ++ tailWord_2106843) baseStart_2106843 baseEnd_2106843 := by
    simpa [prefixWord, tailWord_2106843, baseEnd_2106843] using wordTrace_append hprefix tailTrace_2106843
  have hstable : (prefixWord ++ tailWord_2106843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106843).length < 2 ^ (prefixWord ++ tailWord_2106843).sum := by decide
  have hdescent : baseEnd_2106843 < baseStart_2106843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106881 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_2106881 : Nat := 118140960795 + 2106881 * 2 ^ 59
def prefixEnd_2106881 : Nat := 4983230072969 + 3 ^ 40 * 2106881 * 2
def baseEnd_2106881 : Nat := 1081842634825476552098137

theorem tailTrace_2106881 : CollatzResearch.WordTrace tailWord_2106881 prefixEnd_2106881 1081842634825476552098137 := by
  unfold tailWord_2106881
  simp only [CollatzResearch.WordTrace]
  refine ⟨76844263080137438472648497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51229508720091625648432331 76844263080137438472648497)
  ·
    refine ⟨57633197310103078854486373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76844263080137438472648497 57633197310103078854486373)
    ·
      refine ⟨10806224495644327285216195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57633197310103078854486373 10806224495644327285216195)
      ·
        refine ⟨16209336743466490927824293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806224495644327285216195 16209336743466490927824293)
        ·
          refine ⟨3039250639399967048967055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16209336743466490927824293 3039250639399967048967055)
          ·
            refine ⟨4558875959099950573450583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039250639399967048967055 4558875959099950573450583)
            ·
              refine ⟨6838313938649925860175875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558875959099950573450583 6838313938649925860175875)
              ·
                refine ⟨10257470907974888790263813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838313938649925860175875 10257470907974888790263813)
                ·
                  refine ⟨1923275795245291648174465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10257470907974888790263813 1923275795245291648174465)
                  ·
                    refine ⟨1442456846433968736130849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923275795245291648174465 1442456846433968736130849)
                    ·
                      refine ⟨1081842634825476552098137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442456846433968736130849 1081842634825476552098137)
                      ·
                        rfl

theorem cell23_2106881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_2106881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106881 prefixEnd_2106881 := by exact prefixLift 2106881
  have htrace : WordTrace (prefixWord ++ tailWord_2106881) baseStart_2106881 baseEnd_2106881 := by
    simpa [prefixWord, tailWord_2106881, baseEnd_2106881] using wordTrace_append hprefix tailTrace_2106881
  have hstable : (prefixWord ++ tailWord_2106881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106881).length < 2 ^ (prefixWord ++ tailWord_2106881).sum := by decide
  have hdescent : baseEnd_2106881 < baseStart_2106881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106887 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 7]
def baseStart_2106887 : Nat := 118140960795 + 2106887 * 2 ^ 59
def prefixEnd_2106887 : Nat := 4983230072969 + 3 ^ 40 * 2106887 * 2
def baseEnd_2106887 : Nat := 120205079523267058735901

theorem tailTrace_2106887 : CollatzResearch.WordTrace tailWord_2106887 prefixEnd_2106887 120205079523267058735901 := by
  unfold tailWord_2106887
  simp only [CollatzResearch.WordTrace]
  refine ⟨76844481918115701497366915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51229654612077134331577943 76844481918115701497366915)
  ·
    refine ⟨115266722877173552246050373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76844481918115701497366915 115266722877173552246050373)
    ·
      refine ⟨21612510539470041046134445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115266722877173552246050373 21612510539470041046134445)
      ·
        refine ⟨8104691452301265392300417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21612510539470041046134445 8104691452301265392300417)
        ·
          refine ⟨6078518589225949044225313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8104691452301265392300417 6078518589225949044225313)
          ·
            refine ⟨4558888941919461783168985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078518589225949044225313 4558888941919461783168985)
            ·
              refine ⟨3419166706439596337376739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4558888941919461783168985 3419166706439596337376739)
              ·
                refine ⟨5128750059659394506065109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419166706439596337376739 5128750059659394506065109)
                ·
                  refine ⟨120205079523267058735901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5128750059659394506065109 120205079523267058735901)
                  ·
                    rfl

theorem cell23_2106887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 7].length) (baseStart_2106887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106887 prefixEnd_2106887 := by exact prefixLift 2106887
  have htrace : WordTrace (prefixWord ++ tailWord_2106887) baseStart_2106887 baseEnd_2106887 := by
    simpa [prefixWord, tailWord_2106887, baseEnd_2106887] using wordTrace_append hprefix tailTrace_2106887
  have hstable : (prefixWord ++ tailWord_2106887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106887).length < 2 ^ (prefixWord ++ tailWord_2106887).sum := by decide
  have hdescent : baseEnd_2106887 < baseStart_2106887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106937 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2106937 : Nat := 118140960795 + 2106937 * 2 ^ 59
def prefixEnd_2106937 : Nat := 4983230072969 + 3 ^ 40 * 2106937 * 2
def baseEnd_2106937 : Nat := 1081871389742128332997879

theorem tailTrace_2106937 : CollatzResearch.WordTrace tailWord_2106937 prefixEnd_2106937 1081871389742128332997879 := by
  unfold tailWord_2106937
  simp only [CollatzResearch.WordTrace]
  refine ⟨76846305567934560036687065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51230870378623040024458043 76846305567934560036687065)
  ·
    refine ⟨57634729175950920027515299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76846305567934560036687065 57634729175950920027515299)
    ·
      refine ⟨86452093763926380041272949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57634729175950920027515299 86452093763926380041272949)
      ·
        refine ⟨8104883790368098128869339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86452093763926380041272949 8104883790368098128869339)
        ·
          refine ⟨12157325685552147193304009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104883790368098128869339 12157325685552147193304009)
          ·
            refine ⟨9117994264164110394978007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12157325685552147193304009 9117994264164110394978007)
            ·
              refine ⟨13676991396246165592467011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9117994264164110394978007 13676991396246165592467011)
              ·
                refine ⟨20515487094369248388700517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13676991396246165592467011 20515487094369248388700517)
                ·
                  refine ⟨3846653830194234072881347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20515487094369248388700517 3846653830194234072881347)
                  ·
                    refine ⟨5769980745291351109322021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3846653830194234072881347 5769980745291351109322021)
                    ·
                      refine ⟨1081871389742128332997879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5769980745291351109322021 1081871389742128332997879)
                      ·
                        rfl

theorem cell23_2106937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2106937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106937 prefixEnd_2106937 := by exact prefixLift 2106937
  have htrace : WordTrace (prefixWord ++ tailWord_2106937) baseStart_2106937 baseEnd_2106937 := by
    simpa [prefixWord, tailWord_2106937, baseEnd_2106937] using wordTrace_append hprefix tailTrace_2106937
  have hstable : (prefixWord ++ tailWord_2106937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106937).length < 2 ^ (prefixWord ++ tailWord_2106937).sum := by decide
  have hdescent : baseEnd_2106937 < baseStart_2106937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106994 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_2106994 : Nat := 118140960795 + 2106994 * 2 ^ 59
def prefixEnd_2106994 : Nat := 4983230072969 + 3 ^ 40 * 2106994 * 2
def baseEnd_2106994 : Nat := 120211184237714956665013

theorem tailTrace_2106994 : CollatzResearch.WordTrace tailWord_2106994 prefixEnd_2106994 120211184237714956665013 := by
  unfold tailWord_2106994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19212096132182014692878009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51232256352485372514341357 19212096132182014692878009)
  ·
    refine ⟨14409072099136511019658507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19212096132182014692878009 14409072099136511019658507)
    ·
      refine ⟨21613608148704766529487761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14409072099136511019658507 21613608148704766529487761)
      ·
        refine ⟨16210206111528574897115821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21613608148704766529487761 16210206111528574897115821)
        ·
          refine ⟨6078827291823215586418433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16210206111528574897115821 6078827291823215586418433)
          ·
            refine ⟨4559120468867411689813825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078827291823215586418433 4559120468867411689813825)
            ·
              refine ⟨3419340351650558767360369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4559120468867411689813825 3419340351650558767360369)
              ·
                refine ⟨2564505263737919075520277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419340351650558767360369 2564505263737919075520277)
                ·
                  refine ⟨120211184237714956665013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2564505263737919075520277 120211184237714956665013)
                  ·
                    rfl

theorem cell23_2106994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_2106994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106994 prefixEnd_2106994 := by exact prefixLift 2106994
  have htrace : WordTrace (prefixWord ++ tailWord_2106994) baseStart_2106994 baseEnd_2106994 := by
    simpa [prefixWord, tailWord_2106994, baseEnd_2106994] using wordTrace_append hprefix tailTrace_2106994
  have hstable : (prefixWord ++ tailWord_2106994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106994).length < 2 ^ (prefixWord ++ tailWord_2106994).sum := by decide
  have hdescent : baseEnd_2106994 < baseStart_2106994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106998 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_2106998 : Nat := 118140960795 + 2106998 * 2 ^ 59
def prefixEnd_2106998 : Nat := 4983230072969 + 3 ^ 40 * 2106998 * 2
def baseEnd_2106998 : Nat := 360634237354017531445033

theorem tailTrace_2106998 : CollatzResearch.WordTrace tailWord_2106998 prefixEnd_2106998 360634237354017531445033 := by
  unfold tailWord_2106998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803033151294597965916103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51232353613809044969771765 4803033151294597965916103)
  ·
    refine ⟨7204549726941896948874155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4803033151294597965916103 7204549726941896948874155)
    ·
      refine ⟨10806824590412845423311233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204549726941896948874155 10806824590412845423311233)
      ·
        refine ⟨8105118442809634067483425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10806824590412845423311233 8105118442809634067483425)
        ·
          refine ⟨6078838832107225550612569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8105118442809634067483425 6078838832107225550612569)
          ·
            refine ⟨4559129124080419162959427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078838832107225550612569 4559129124080419162959427)
            ·
              refine ⟨6838693686120628744439141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559129124080419162959427 6838693686120628744439141)
              ·
                refine ⟨1282255066147617889582339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6838693686120628744439141 1282255066147617889582339)
                ·
                  refine ⟨1923382599221426834373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282255066147617889582339 1923382599221426834373509)
                  ·
                    refine ⟨360634237354017531445033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923382599221426834373509 360634237354017531445033)
                    ·
                      rfl

theorem cell23_2106998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_2106998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2106998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2106998 prefixEnd_2106998 := by exact prefixLift 2106998
  have htrace : WordTrace (prefixWord ++ tailWord_2106998) baseStart_2106998 baseEnd_2106998 := by
    simpa [prefixWord, tailWord_2106998, baseEnd_2106998] using wordTrace_append hprefix tailTrace_2106998
  have hstable : (prefixWord ++ tailWord_2106998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106998).length < 2 ^ (prefixWord ++ tailWord_2106998).sum := by decide
  have hdescent : baseEnd_2106998 < baseStart_2106998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107000 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2107000 : Nat := 118140960795 + 2107000 * 2 ^ 59
def prefixEnd_2107000 : Nat := 4983230072969 + 3 ^ 40 * 2107000 * 2
def baseEnd_2107000 : Nat := 1081903739023361586510089

theorem tailTrace_2107000 : CollatzResearch.WordTrace tailWord_2107000 prefixEnd_2107000 1081903739023361586510089 := by
  unfold tailWord_2107000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38424301683353160898115227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51232402244470881197486969 38424301683353160898115227)
  ·
    refine ⟨57636452525029741347172841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38424301683353160898115227 57636452525029741347172841)
    ·
      refine ⟨43227339393772306010379631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57636452525029741347172841 43227339393772306010379631)
      ·
        refine ⟨64841009090658459015569447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43227339393772306010379631 64841009090658459015569447)
        ·
          refine ⟨97261513635987688523354171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64841009090658459015569447 97261513635987688523354171)
          ·
            refine ⟨145892270453981532785031257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97261513635987688523354171 145892270453981532785031257)
            ·
              refine ⟨109419202840486149588773443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145892270453981532785031257 109419202840486149588773443)
              ·
                refine ⟨164128804260729224383160165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109419202840486149588773443 164128804260729224383160165)
                ·
                  refine ⟨30774150798886729571842531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164128804260729224383160165 30774150798886729571842531)
                  ·
                    refine ⟨46161226198330094357763797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30774150798886729571842531 46161226198330094357763797)
                    ·
                      refine ⟨1081903739023361586510089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46161226198330094357763797 1081903739023361586510089)
                      ·
                        rfl

theorem cell23_2107000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2107000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107000 prefixEnd_2107000 := by exact prefixLift 2107000
  have htrace : WordTrace (prefixWord ++ tailWord_2107000) baseStart_2107000 baseEnd_2107000 := by
    simpa [prefixWord, tailWord_2107000, baseEnd_2107000] using wordTrace_append hprefix tailTrace_2107000
  have hstable : (prefixWord ++ tailWord_2107000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107000).length < 2 ^ (prefixWord ++ tailWord_2107000).sum := by decide
  have hdescent : baseEnd_2107000 < baseStart_2107000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107004 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_2107004 : Nat := 118140960795 + 2107004 * 2 ^ 59
def prefixEnd_2107004 : Nat := 4983230072969 + 3 ^ 40 * 2107004 * 2
def baseEnd_2107004 : Nat := 1081905792945979570860071

theorem tailTrace_2107004 : CollatzResearch.WordTrace tailWord_2107004 prefixEnd_2107004 1081905792945979570860071 := by
  unfold tailWord_2107004
  simp only [CollatzResearch.WordTrace]
  refine ⟨38424374629345915239688033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51232499505794553652917377 38424374629345915239688033)
  ·
    refine ⟨28818280972009436429766025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38424374629345915239688033 28818280972009436429766025)
    ·
      refine ⟨21613710729007077322324519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28818280972009436429766025 21613710729007077322324519)
      ·
        refine ⟨32420566093510615983486779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21613710729007077322324519 32420566093510615983486779)
        ·
          refine ⟨48630849140265923975230169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32420566093510615983486779 48630849140265923975230169)
          ·
            refine ⟨36473136855199442981422627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48630849140265923975230169 36473136855199442981422627)
            ·
              refine ⟨54709705282799164472133941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36473136855199442981422627 54709705282799164472133941)
              ·
                refine ⟨5129034870262421669262557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54709705282799164472133941 5129034870262421669262557)
                ·
                  refine ⟨1923388076348408125973459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5129034870262421669262557 1923388076348408125973459)
                  ·
                    refine ⟨2885082114522612188960189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1923388076348408125973459 2885082114522612188960189)
                    ·
                      refine ⟨1081905792945979570860071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2885082114522612188960189 1081905792945979570860071)
                      ·
                        rfl

theorem cell23_2107004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_2107004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107004 prefixEnd_2107004 := by exact prefixLift 2107004
  have htrace : WordTrace (prefixWord ++ tailWord_2107004) baseStart_2107004 baseEnd_2107004 := by
    simpa [prefixWord, tailWord_2107004, baseEnd_2107004] using wordTrace_append hprefix tailTrace_2107004
  have hstable : (prefixWord ++ tailWord_2107004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107004).length < 2 ^ (prefixWord ++ tailWord_2107004).sum := by decide
  have hdescent : baseEnd_2107004 < baseStart_2107004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107031 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_2107031 : Nat := 118140960795 + 2107031 * 2 ^ 59
def prefixEnd_2107031 : Nat := 4983230072969 + 3 ^ 40 * 2107031 * 2
def baseEnd_2107031 : Nat := 1081919656923650965222447

theorem tailTrace_2107031 : CollatzResearch.WordTrace tailWord_2107031 prefixEnd_2107031 1081919656923650965222447 := by
  unfold tailWord_2107031
  simp only [CollatzResearch.WordTrace]
  refine ⟨76849734029594014090608947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51233156019729342727072631 76849734029594014090608947)
  ·
    refine ⟨115274601044391021135913421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76849734029594014090608947 115274601044391021135913421)
    ·
      refine ⟨43227975391646632925967533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115274601044391021135913421 43227975391646632925967533)
      ·
        refine ⟨16210490771867487347237825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43227975391646632925967533 16210490771867487347237825)
        ·
          refine ⟨12157868078900615510428369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16210490771867487347237825 12157868078900615510428369)
          ·
            refine ⟨9118401059175461632821277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12157868078900615510428369 9118401059175461632821277)
            ·
              refine ⟨3419400397190798112307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9118401059175461632821277 3419400397190798112307979)
              ·
                refine ⟨5129100595786197168461969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419400397190798112307979 5129100595786197168461969)
                ·
                  refine ⟨3846825446839647876346477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5129100595786197168461969 3846825446839647876346477)
                  ·
                    refine ⟨1442559542564867953629929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3846825446839647876346477 1442559542564867953629929)
                    ·
                      refine ⟨1081919656923650965222447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442559542564867953629929 1081919656923650965222447)
                      ·
                        rfl

theorem cell23_2107031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_2107031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107031 prefixEnd_2107031 := by exact prefixLift 2107031
  have htrace : WordTrace (prefixWord ++ tailWord_2107031) baseStart_2107031 baseEnd_2107031 := by
    simpa [prefixWord, tailWord_2107031, baseEnd_2107031] using wordTrace_append hprefix tailTrace_2107031
  have hstable : (prefixWord ++ tailWord_2107031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107031).length < 2 ^ (prefixWord ++ tailWord_2107031).sum := by decide
  have hdescent : baseEnd_2107031 < baseStart_2107031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107041 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2107041 : Nat := 118140960795 + 2107041 * 2 ^ 59
def prefixEnd_2107041 : Nat := 4983230072969 + 3 ^ 40 * 2107041 * 2
def baseEnd_2107041 : Nat := 360641597243398642032467

theorem tailTrace_2107041 : CollatzResearch.WordTrace tailWord_2107041 prefixEnd_2107041 360641597243398642032467 := by
  unfold tailWord_2107041
  simp only [CollatzResearch.WordTrace]
  refine ⟨76850098759557785798472977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51233399173038523865648651 76850098759557785798472977)
  ·
    refine ⟨57637574069668339348854733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76850098759557785798472977 57637574069668339348854733)
    ·
      refine ⟨21614090276125627255820525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57637574069668339348854733 21614090276125627255820525)
      ·
        refine ⟨8105283853547110220932697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21614090276125627255820525 8105283853547110220932697)
        ·
          refine ⟨6078962890160332665699523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8105283853547110220932697 6078962890160332665699523)
          ·
            refine ⟨9118444335240498998549285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078962890160332665699523 9118444335240498998549285)
            ·
              refine ⟨1709708312857593562227991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9118444335240498998549285 1709708312857593562227991)
              ·
                refine ⟨2564562469286390343341987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709708312857593562227991 2564562469286390343341987)
                ·
                  refine ⟨3846843703929585515012981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564562469286390343341987 3846843703929585515012981)
                  ·
                    refine ⟨360641597243398642032467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3846843703929585515012981 360641597243398642032467)
                    ·
                      rfl

theorem cell23_2107041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2107041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107041 prefixEnd_2107041 := by exact prefixLift 2107041
  have htrace : WordTrace (prefixWord ++ tailWord_2107041) baseStart_2107041 baseEnd_2107041 := by
    simpa [prefixWord, tailWord_2107041, baseEnd_2107041] using wordTrace_append hprefix tailTrace_2107041
  have hstable : (prefixWord ++ tailWord_2107041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107041).length < 2 ^ (prefixWord ++ tailWord_2107041).sum := by decide
  have hdescent : baseEnd_2107041 < baseStart_2107041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107071 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 2, 4]
def baseStart_2107071 : Nat := 118140960795 + 2107071 * 2 ^ 59
def prefixEnd_2107071 : Nat := 4983230072969 + 3 ^ 40 * 2107071 * 2
def baseEnd_2107071 : Nat := 360646732049943602907421

theorem tailTrace_2107071 : CollatzResearch.WordTrace tailWord_2107071 prefixEnd_2107071 360646732049943602907421 := by
  unfold tailWord_2107071
  simp only [CollatzResearch.WordTrace]
  refine ⟨76851192949449100922065067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51234128632966067281376711 76851192949449100922065067)
  ·
    refine ⟨115276789424173651383097601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76851192949449100922065067 115276789424173651383097601)
    ·
      refine ⟨86457592068130238537323201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115276789424173651383097601 86457592068130238537323201)
      ·
        refine ⟨64843194051097678902992401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86457592068130238537323201 64843194051097678902992401)
        ·
          refine ⟨48632395538323259177244301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64843194051097678902992401 48632395538323259177244301)
          ·
            refine ⟨18237148326871222191466613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48632395538323259177244301 18237148326871222191466613)
            ·
              refine ⟨1709732655644177080449995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18237148326871222191466613 1709732655644177080449995)
              ·
                refine ⟨2564598983466265620674993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709732655644177080449995 2564598983466265620674993)
                ·
                  refine ⟨1923449237599699215506245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2564598983466265620674993 1923449237599699215506245)
                  ·
                    refine ⟨360646732049943602907421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923449237599699215506245 360646732049943602907421)
                    ·
                      rfl

theorem cell23_2107071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_2107071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107071 prefixEnd_2107071 := by exact prefixLift 2107071
  have htrace : WordTrace (prefixWord ++ tailWord_2107071) baseStart_2107071 baseEnd_2107071 := by
    simpa [prefixWord, tailWord_2107071, baseEnd_2107071] using wordTrace_append hprefix tailTrace_2107071
  have hstable : (prefixWord ++ tailWord_2107071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107071).length < 2 ^ (prefixWord ++ tailWord_2107071).sum := by decide
  have hdescent : baseEnd_2107071 < baseStart_2107071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107084 : List Nat := [2, 2, 1, 5, 2, 1, 1, 9]
def baseStart_2107084 : Nat := 118140960795 + 2107084 * 2 ^ 59
def prefixEnd_2107084 : Nat := 4983230072969 + 3 ^ 40 * 2107084 * 2
def baseEnd_2107084 : Nat := 40072106348086639179989

theorem tailTrace_2107084 : CollatzResearch.WordTrace tailWord_2107084 prefixEnd_2107084 40072106348086639179989 := by
  unfold tailWord_2107084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38425833549201002071144153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51234444732268002761525537 38425833549201002071144153)
  ·
    refine ⟨28819375161900751553358115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38425833549201002071144153 28819375161900751553358115)
    ·
      refine ⟨43229062742851127330037173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28819375161900751553358115 43229062742851127330037173)
      ·
        refine ⟨4052724632142293187190985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43229062742851127330037173 4052724632142293187190985)
        ·
          refine ⟨3039543474106719890393239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4052724632142293187190985 3039543474106719890393239)
          ·
            refine ⟨4559315211160079835589859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039543474106719890393239 4559315211160079835589859)
            ·
              refine ⟨6838972816740119753384789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559315211160079835589859 6838972816740119753384789)
              ·
                refine ⟨40072106348086639179989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6838972816740119753384789 40072106348086639179989)
                ·
                  rfl

theorem cell23_2107084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 9].length) (baseStart_2107084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107084 prefixEnd_2107084 := by exact prefixLift 2107084
  have htrace : WordTrace (prefixWord ++ tailWord_2107084) baseStart_2107084 baseEnd_2107084 := by
    simpa [prefixWord, tailWord_2107084, baseEnd_2107084] using wordTrace_append hprefix tailTrace_2107084
  have hstable : (prefixWord ++ tailWord_2107084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107084).length < 2 ^ (prefixWord ++ tailWord_2107084).sum := by decide
  have hdescent : baseEnd_2107084 < baseStart_2107084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107101 : List Nat := [1, 4, 3, 3, 1, 2, 9]
def baseStart_2107101 : Nat := 118140960795 + 2107101 * 2 ^ 59
def prefixEnd_2107101 : Nat := 4983230072969 + 3 ^ 40 * 2107101 * 2
def baseEnd_2107101 : Nat := 13357476550240317177125

theorem tailTrace_2107101 : CollatzResearch.WordTrace tailWord_2107101 prefixEnd_2107101 13357476550240317177125 := by
  unfold tailWord_2107101
  simp only [CollatzResearch.WordTrace]
  refine ⟨76852287139340416045657157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51234858092893610697104771 76852287139340416045657157)
  ·
    refine ⟨14409803838626328008560717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76852287139340416045657157 14409803838626328008560717)
    ·
      refine ⟨5403676439484873003210269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14409803838626328008560717 5403676439484873003210269)
      ·
        refine ⟨2026378664806827376203851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5403676439484873003210269 2026378664806827376203851)
        ·
          refine ⟨3039567997210241064305777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026378664806827376203851 3039567997210241064305777)
          ·
            refine ⟨2279675997907680798229333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3039567997210241064305777 2279675997907680798229333)
            ·
              refine ⟨13357476550240317177125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2279675997907680798229333 13357476550240317177125)
              ·
                rfl

theorem cell23_2107101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 9].length) (baseStart_2107101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107101 prefixEnd_2107101 := by exact prefixLift 2107101
  have htrace : WordTrace (prefixWord ++ tailWord_2107101) baseStart_2107101 baseEnd_2107101 := by
    simpa [prefixWord, tailWord_2107101, baseEnd_2107101] using wordTrace_append hprefix tailTrace_2107101
  have hstable : (prefixWord ++ tailWord_2107101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107101).length < 2 ^ (prefixWord ++ tailWord_2107101).sum := by decide
  have hdescent : baseEnd_2107101 < baseStart_2107101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107112 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2107112 : Nat := 118140960795 + 2107112 * 2 ^ 59
def prefixEnd_2107112 : Nat := 4983230072969 + 3 ^ 40 * 2107112 * 2
def baseEnd_2107112 : Nat := 1081961248856665148309575

theorem tailTrace_2107112 : CollatzResearch.WordTrace tailWord_2107112 prefixEnd_2107112 1081961248856665148309575 := by
  unfold tailWord_2107112
  simp only [CollatzResearch.WordTrace]
  refine ⟨38426344171150282462153795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51235125561533709949538393 38426344171150282462153795)
  ·
    refine ⟨57639516256725423693230693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38426344171150282462153795 57639516256725423693230693)
    ·
      refine ⟨10807409298136016942480755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57639516256725423693230693 10807409298136016942480755)
      ·
        refine ⟨16211113947204025413721133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10807409298136016942480755 16211113947204025413721133)
        ·
          refine ⟨6079167730201509530145425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16211113947204025413721133 6079167730201509530145425)
          ·
            refine ⟨4559375797651132147609069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6079167730201509530145425 4559375797651132147609069)
            ·
              refine ⟨1709765924119174555353401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4559375797651132147609069 1709765924119174555353401)
              ·
                refine ⟨1282324443089380916515051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709765924119174555353401 1282324443089380916515051)
                ·
                  refine ⟨1923486664634071374772577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282324443089380916515051 1923486664634071374772577)
                  ·
                    refine ⟨1442614998475553531079433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923486664634071374772577 1442614998475553531079433)
                    ·
                      refine ⟨1081961248856665148309575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442614998475553531079433 1081961248856665148309575)
                      ·
                        rfl

theorem cell23_2107112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2107112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107112 prefixEnd_2107112 := by exact prefixLift 2107112
  have htrace : WordTrace (prefixWord ++ tailWord_2107112) baseStart_2107112 baseEnd_2107112 := by
    simpa [prefixWord, tailWord_2107112, baseEnd_2107112] using wordTrace_append hprefix tailTrace_2107112
  have hstable : (prefixWord ++ tailWord_2107112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107112).length < 2 ^ (prefixWord ++ tailWord_2107112).sum := by decide
  have hdescent : baseEnd_2107112 < baseStart_2107112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107127 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 2, 6]
def baseStart_2107127 : Nat := 118140960795 + 2107127 * 2 ^ 59
def prefixEnd_2107127 : Nat := 4983230072969 + 3 ^ 40 * 2107127 * 2
def baseEnd_2107127 : Nat := 360656317022160863207335

theorem tailTrace_2107127 : CollatzResearch.WordTrace tailWord_2107127 prefixEnd_2107127 360656317022160863207335 := by
  unfold tailWord_2107127
  simp only [CollatzResearch.WordTrace]
  refine ⟨76853235437246222486103635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51235490291497481657402423 76853235437246222486103635)
  ·
    refine ⟨115279853155869333729155453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76853235437246222486103635 115279853155869333729155453)
    ·
      refine ⟨43229944933451000148433295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115279853155869333729155453 43229944933451000148433295)
      ·
        refine ⟨64844917400176500222649943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43229944933451000148433295 64844917400176500222649943)
        ·
          refine ⟨97267376100264750333974915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64844917400176500222649943 97267376100264750333974915)
          ·
            refine ⟨145901064150397125500962373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97267376100264750333974915 145901064150397125500962373)
            ·
              refine ⟨27356449528199461031430445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145901064150397125500962373 27356449528199461031430445)
              ·
                refine ⟨10258668573074797886786417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27356449528199461031430445 10258668573074797886786417)
                ·
                  refine ⟨7694001429806098415089813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10258668573074797886786417 7694001429806098415089813)
                  ·
                    refine ⟨360656317022160863207335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7694001429806098415089813 360656317022160863207335)
                    ·
                      rfl

theorem cell23_2107127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_2107127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107127 prefixEnd_2107127 := by exact prefixLift 2107127
  have htrace : WordTrace (prefixWord ++ tailWord_2107127) baseStart_2107127 baseEnd_2107127 := by
    simpa [prefixWord, tailWord_2107127, baseEnd_2107127] using wordTrace_append hprefix tailTrace_2107127
  have hstable : (prefixWord ++ tailWord_2107127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107127).length < 2 ^ (prefixWord ++ tailWord_2107127).sum := by decide
  have hdescent : baseEnd_2107127 < baseStart_2107127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107138 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2107138 : Nat := 118140960795 + 2107138 * 2 ^ 59
def prefixEnd_2107138 : Nat := 4983230072969 + 3 ^ 40 * 2107138 * 2
def baseEnd_2107138 : Nat := 1081974599353682046584455

theorem tailTrace_2107138 : CollatzResearch.WordTrace tailWord_2107138 prefixEnd_2107138 1081974599353682046584455 := by
  unfold tailWord_2107138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19213409160051592841188517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51235757760137580909836045 19213409160051592841188517)
  ·
    refine ⟨3602514217509673657722847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19213409160051592841188517 3602514217509673657722847)
    ·
      refine ⟨5403771326264510486584271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602514217509673657722847 5403771326264510486584271)
      ·
        refine ⟨8105656989396765729876407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5403771326264510486584271 8105656989396765729876407)
        ·
          refine ⟨12158485484095148594814611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8105656989396765729876407 12158485484095148594814611)
          ·
            refine ⟨18237728226142722892221917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12158485484095148594814611 18237728226142722892221917)
            ·
              refine ⟨6839148084803521084583219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18237728226142722892221917 6839148084803521084583219)
              ·
                refine ⟨10258722127205281626874829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839148084803521084583219 10258722127205281626874829)
                ·
                  refine ⟨3847020797701980610078061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10258722127205281626874829 3847020797701980610078061)
                  ·
                    refine ⟨1442632799138242728779273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3847020797701980610078061 1442632799138242728779273)
                    ·
                      refine ⟨1081974599353682046584455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442632799138242728779273 1081974599353682046584455)
                      ·
                        rfl

theorem cell23_2107138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2107138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107138 prefixEnd_2107138 := by exact prefixLift 2107138
  have htrace : WordTrace (prefixWord ++ tailWord_2107138) baseStart_2107138 baseEnd_2107138 := by
    simpa [prefixWord, tailWord_2107138, baseEnd_2107138] using wordTrace_append hprefix tailTrace_2107138
  have hstable : (prefixWord ++ tailWord_2107138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107138).length < 2 ^ (prefixWord ++ tailWord_2107138).sum := by decide
  have hdescent : baseEnd_2107138 < baseStart_2107138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107149 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2107149 : Nat := 118140960795 + 2107149 * 2 ^ 59
def prefixEnd_2107149 : Nat := 4983230072969 + 3 ^ 40 * 2107149 * 2
def baseEnd_2107149 : Nat := 1081980247640881503546905

theorem tailTrace_2107149 : CollatzResearch.WordTrace tailWord_2107149 prefixEnd_2107149 1081980247640881503546905 := by
  unfold tailWord_2107149
  simp only [CollatzResearch.WordTrace]
  refine ⟨76854037843166520243404501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51236025228777680162269667 76854037843166520243404501)
  ·
    refine ⟨1801266511949215318204793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 76854037843166520243404501 1801266511949215318204793)
    ·
      refine ⟨1350949883961911488653595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1801266511949215318204793 1350949883961911488653595)
      ·
        refine ⟨2026424825942867232980393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350949883961911488653595 2026424825942867232980393)
        ·
          refine ⟨1519818619457150424735295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2026424825942867232980393 1519818619457150424735295)
          ·
            refine ⟨2279727929185725637102943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519818619457150424735295 2279727929185725637102943)
            ·
              refine ⟨3419591893778588455654415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279727929185725637102943 3419591893778588455654415)
              ·
                refine ⟨5129387840667882683481623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419591893778588455654415 5129387840667882683481623)
                ·
                  refine ⟨7694081761001824025222435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129387840667882683481623 7694081761001824025222435)
                  ·
                    refine ⟨11541122641502736037833653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7694081761001824025222435 11541122641502736037833653)
                    ·
                      refine ⟨1081980247640881503546905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11541122641502736037833653 1081980247640881503546905)
                      ·
                        rfl

theorem cell23_2107149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2107149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107149 prefixEnd_2107149 := by exact prefixLift 2107149
  have htrace : WordTrace (prefixWord ++ tailWord_2107149) baseStart_2107149 baseEnd_2107149 := by
    simpa [prefixWord, tailWord_2107149, baseEnd_2107149] using wordTrace_append hprefix tailTrace_2107149
  have hstable : (prefixWord ++ tailWord_2107149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107149).length < 2 ^ (prefixWord ++ tailWord_2107149).sum := by decide
  have hdescent : baseEnd_2107149 < baseStart_2107149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107151 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 4, 2, 2]
def baseStart_2107151 : Nat := 118140960795 + 2107151 * 2 ^ 59
def prefixEnd_2107151 : Nat := 4983230072969 + 3 ^ 40 * 2107151 * 2
def baseEnd_2107151 : Nat := 1081981274602190495721895

theorem tailTrace_2107151 : CollatzResearch.WordTrace tailWord_2107151 prefixEnd_2107151 1081981274602190495721895 := by
  unfold tailWord_2107151
  simp only [CollatzResearch.WordTrace]
  refine ⟨76854110789159274584977307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51236073859439516389984871 76854110789159274584977307)
  ·
    refine ⟨115281166183738911877465961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76854110789159274584977307 115281166183738911877465961)
    ·
      refine ⟨86460874637804183908099471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115281166183738911877465961 86460874637804183908099471)
      ·
        refine ⟨129691311956706275862149207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86460874637804183908099471 129691311956706275862149207)
        ·
          refine ⟨194536967935059413793223811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129691311956706275862149207 194536967935059413793223811)
          ·
            refine ⟨291805451902589120689835717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194536967935059413793223811 291805451902589120689835717)
            ·
              refine ⟨54713522231735460129344197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 291805451902589120689835717 54713522231735460129344197)
              ·
                refine ⟨10258785418450398774252037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54713522231735460129344197 10258785418450398774252037)
                ·
                  refine ⟨1923522265959449770172257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10258785418450398774252037 1923522265959449770172257)
                  ·
                    refine ⟨1442641699469587327629193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923522265959449770172257 1442641699469587327629193)
                    ·
                      refine ⟨1081981274602190495721895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442641699469587327629193 1081981274602190495721895)
                      ·
                        rfl

theorem cell23_2107151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2, 2].length) (baseStart_2107151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107151 prefixEnd_2107151 := by exact prefixLift 2107151
  have htrace : WordTrace (prefixWord ++ tailWord_2107151) baseStart_2107151 baseEnd_2107151 := by
    simpa [prefixWord, tailWord_2107151, baseEnd_2107151] using wordTrace_append hprefix tailTrace_2107151
  have hstable : (prefixWord ++ tailWord_2107151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107151).length < 2 ^ (prefixWord ++ tailWord_2107151).sum := by decide
  have hdescent : baseEnd_2107151 < baseStart_2107151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107164 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2107164 : Nat := 118140960795 + 2107164 * 2 ^ 59
def prefixEnd_2107164 : Nat := 4983230072969 + 3 ^ 40 * 2107164 * 2
def baseEnd_2107164 : Nat := 1081987949850698944859335

theorem tailTrace_2107164 : CollatzResearch.WordTrace tailWord_2107164 prefixEnd_2107164 1081987949850698944859335 := by
  unfold tailWord_2107164
  simp only [CollatzResearch.WordTrace]
  refine ⟨38427292469056088902600273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51236389958741451870133697 38427292469056088902600273)
  ·
    refine ⟨28820469351792066676950205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38427292469056088902600273 28820469351792066676950205)
    ·
      refine ⟨10807676006922025003856327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28820469351792066676950205 10807676006922025003856327)
      ·
        refine ⟨16211514010383037505784491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10807676006922025003856327 16211514010383037505784491)
        ·
          refine ⟨24317271015574556258676737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16211514010383037505784491 24317271015574556258676737)
          ·
            refine ⟨18237953261680917194007553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24317271015574556258676737 18237953261680917194007553)
            ·
              refine ⟨13678464946260687895505665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18237953261680917194007553 13678464946260687895505665)
              ·
                refine ⟨10258848709695515921629249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13678464946260687895505665 10258848709695515921629249)
                ·
                  refine ⟨7694136532271636941221937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10258848709695515921629249 7694136532271636941221937)
                  ·
                    refine ⟨5770602399203727705916453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7694136532271636941221937 5770602399203727705916453)
                    ·
                      refine ⟨1081987949850698944859335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5770602399203727705916453 1081987949850698944859335)
                      ·
                        rfl

theorem cell23_2107164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2107164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107164 prefixEnd_2107164 := by exact prefixLift 2107164
  have htrace : WordTrace (prefixWord ++ tailWord_2107164) baseStart_2107164 baseEnd_2107164 := by
    simpa [prefixWord, tailWord_2107164, baseEnd_2107164] using wordTrace_append hprefix tailTrace_2107164
  have hstable : (prefixWord ++ tailWord_2107164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107164).length < 2 ^ (prefixWord ++ tailWord_2107164).sum := by decide
  have hdescent : baseEnd_2107164 < baseStart_2107164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107227 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_2107227 : Nat := 118140960795 + 2107227 * 2 ^ 59
def prefixEnd_2107227 : Nat := 4983230072969 + 3 ^ 40 * 2107227 * 2
def baseEnd_2107227 : Nat := 1082020299131932198371545

theorem tailTrace_2107227 : CollatzResearch.WordTrace tailWord_2107227 prefixEnd_2107227 1082020299131932198371545 := by
  unfold tailWord_2107227
  simp only [CollatzResearch.WordTrace]
  refine ⟨76856882736883939564743935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51237921824589293043162623 76856882736883939564743935)
  ·
    refine ⟨115285324105325909347115903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76856882736883939564743935 115285324105325909347115903)
    ·
      refine ⟨172927986157988864020673855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115285324105325909347115903 172927986157988864020673855)
      ·
        refine ⟨259391979236983296031010783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172927986157988864020673855 259391979236983296031010783)
        ·
          refine ⟨389087968855474944046516175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259391979236983296031010783 389087968855474944046516175)
          ·
            refine ⟨583631953283212416069774263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389087968855474944046516175 583631953283212416069774263)
            ·
              refine ⟨875447929924818624104661395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583631953283212416069774263 875447929924818624104661395)
              ·
                refine ⟨1313171894887227936156992093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875447929924818624104661395 1313171894887227936156992093)
                ·
                  refine ⟨492439460582710476058872035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1313171894887227936156992093 492439460582710476058872035)
                  ·
                    refine ⟨738659190874065714088308053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 492439460582710476058872035 738659190874065714088308053)
                    ·
                      refine ⟨1082020299131932198371545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 738659190874065714088308053 1082020299131932198371545)
                      ·
                        rfl

theorem cell23_2107227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_2107227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107227 prefixEnd_2107227 := by exact prefixLift 2107227
  have htrace : WordTrace (prefixWord ++ tailWord_2107227) baseStart_2107227 baseEnd_2107227 := by
    simpa [prefixWord, tailWord_2107227, baseEnd_2107227] using wordTrace_append hprefix tailTrace_2107227
  have hstable : (prefixWord ++ tailWord_2107227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107227).length < 2 ^ (prefixWord ++ tailWord_2107227).sum := by decide
  have hdescent : baseEnd_2107227 < baseStart_2107227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107261 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2107261 : Nat := 118140960795 + 2107261 * 2 ^ 59
def prefixEnd_2107261 : Nat := 4983230072969 + 3 ^ 40 * 2107261 * 2
def baseEnd_2107261 : Nat := 1082037757474185065346389

theorem tailTrace_2107261 : CollatzResearch.WordTrace tailWord_2107261 prefixEnd_2107261 1082037757474185065346389 := by
  unfold tailWord_2107261
  simp only [CollatzResearch.WordTrace]
  refine ⟨76858122818760763371481637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51238748545840508914321091 76858122818760763371481637)
  ·
    refine ⟨14410898028517643132152807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76858122818760763371481637 14410898028517643132152807)
    ·
      refine ⟨21616347042776464698229211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14410898028517643132152807 21616347042776464698229211)
      ·
        refine ⟨32424520564164697047343817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21616347042776464698229211 32424520564164697047343817)
        ·
          refine ⟨24318390423123522785507863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32424520564164697047343817 24318390423123522785507863)
          ·
            refine ⟨36477585634685284178261795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24318390423123522785507863 36477585634685284178261795)
            ·
              refine ⟨54716378452027926267392693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36477585634685284178261795 54716378452027926267392693)
              ·
                refine ⟨5129660479877618087568065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54716378452027926267392693 5129660479877618087568065)
                ·
                  refine ⟨3847245359908213565676049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5129660479877618087568065 3847245359908213565676049)
                  ·
                    refine ⟨2885434019931160174257037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847245359908213565676049 2885434019931160174257037)
                    ·
                      refine ⟨1082037757474185065346389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2885434019931160174257037 1082037757474185065346389)
                      ·
                        rfl

theorem cell23_2107261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2107261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107261 prefixEnd_2107261 := by exact prefixLift 2107261
  have htrace : WordTrace (prefixWord ++ tailWord_2107261) baseStart_2107261 baseEnd_2107261 := by
    simpa [prefixWord, tailWord_2107261, baseEnd_2107261] using wordTrace_append hprefix tailTrace_2107261
  have hstable : (prefixWord ++ tailWord_2107261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107261).length < 2 ^ (prefixWord ++ tailWord_2107261).sum := by decide
  have hdescent : baseEnd_2107261 < baseStart_2107261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107285 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2107285 : Nat := 118140960795 + 2107285 * 2 ^ 59
def prefixEnd_2107285 : Nat := 4983230072969 + 3 ^ 40 * 2107285 * 2
def baseEnd_2107285 : Nat := 360683360336630990482093

theorem tailTrace_2107285 : CollatzResearch.WordTrace tailWord_2107285 prefixEnd_2107285 360683360336630990482093 := by
  unfold tailWord_2107285
  simp only [CollatzResearch.WordTrace]
  refine ⟨76858998170673815470355309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51239332113782543646903539 76858998170673815470355309)
  ·
    refine ⟨28822124314002680801383241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76858998170673815470355309 28822124314002680801383241)
    ·
      refine ⟨21616593235502010601037431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28822124314002680801383241 21616593235502010601037431)
      ·
        refine ⟨32424889853253015901556147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21616593235502010601037431 32424889853253015901556147)
        ·
          refine ⟨48637334779879523852334221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32424889853253015901556147 48637334779879523852334221)
          ·
            refine ⟨18239000542454821444625333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48637334779879523852334221 18239000542454821444625333)
            ·
              refine ⟨1709906300855139510433625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18239000542454821444625333 1709906300855139510433625)
              ·
                refine ⟨1282429725641354632825219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709906300855139510433625 1282429725641354632825219)
                ·
                  refine ⟨1923644588462031949237829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282429725641354632825219 1923644588462031949237829)
                  ·
                    refine ⟨360683360336630990482093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923644588462031949237829 360683360336630990482093)
                    ·
                      rfl

theorem cell23_2107285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2107285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107285 prefixEnd_2107285 := by exact prefixLift 2107285
  have htrace : WordTrace (prefixWord ++ tailWord_2107285) baseStart_2107285 baseEnd_2107285 := by
    simpa [prefixWord, tailWord_2107285, baseEnd_2107285] using wordTrace_append hprefix tailTrace_2107285
  have hstable : (prefixWord ++ tailWord_2107285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107285).length < 2 ^ (prefixWord ++ tailWord_2107285).sum := by decide
  have hdescent : baseEnd_2107285 < baseStart_2107285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107298 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_2107298 : Nat := 118140960795 + 2107298 * 2 ^ 59
def prefixEnd_2107298 : Nat := 4983230072969 + 3 ^ 40 * 2107298 * 2
def baseEnd_2107298 : Nat := 120228528473155713398191

theorem tailTrace_2107298 : CollatzResearch.WordTrace tailWord_2107298 prefixEnd_2107298 120228528473155713398191 := by
  unfold tailWord_2107298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19214868079906679672644637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51239648213084479127052365 19214868079906679672644637)
  ·
    refine ⟨7205575529965004877241739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19214868079906679672644637 7205575529965004877241739)
    ·
      refine ⟨10808363294947507315862609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7205575529965004877241739 10808363294947507315862609)
      ·
        refine ⟨8106272471210630486896957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10808363294947507315862609 8106272471210630486896957)
        ·
          refine ⟨3039852176703986432586359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8106272471210630486896957 3039852176703986432586359)
          ·
            refine ⟨4559778265055979648879539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039852176703986432586359 4559778265055979648879539)
            ·
              refine ⟨6839667397583969473319309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559778265055979648879539 6839667397583969473319309)
              ·
                refine ⟨2564875274093988552494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6839667397583969473319309 2564875274093988552494741)
                ·
                  refine ⟨120228528473155713398191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2564875274093988552494741 120228528473155713398191)
                  ·
                    rfl

theorem cell23_2107298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_2107298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107298 prefixEnd_2107298 := by exact prefixLift 2107298
  have htrace : WordTrace (prefixWord ++ tailWord_2107298) baseStart_2107298 baseEnd_2107298 := by
    simpa [prefixWord, tailWord_2107298, baseEnd_2107298] using wordTrace_append hprefix tailTrace_2107298
  have hstable : (prefixWord ++ tailWord_2107298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107298).length < 2 ^ (prefixWord ++ tailWord_2107298).sum := by decide
  have hdescent : baseEnd_2107298 < baseStart_2107298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107301 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_2107301 : Nat := 118140960795 + 2107301 * 2 ^ 59
def prefixEnd_2107301 : Nat := 4983230072969 + 3 ^ 40 * 2107301 * 2
def baseEnd_2107301 : Nat := 1082058296700364908846205

theorem tailTrace_2107301 : CollatzResearch.WordTrace tailWord_2107301 prefixEnd_2107301 1082058296700364908846205 := by
  unfold tailWord_2107301
  simp only [CollatzResearch.WordTrace]
  refine ⟨76859581738615850202937757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51239721159077233468625171 76859581738615850202937757)
  ·
    refine ⟨28822343151980943826101659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76859581738615850202937757 28822343151980943826101659)
    ·
      refine ⟨43233514727971415739152489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28822343151980943826101659 43233514727971415739152489)
      ·
        refine ⟨32425136045978561804364367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43233514727971415739152489 32425136045978561804364367)
        ·
          refine ⟨48637704068967842706546551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32425136045978561804364367 48637704068967842706546551)
          ·
            refine ⟨72956556103451764059819827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48637704068967842706546551 72956556103451764059819827)
            ·
              refine ⟨109434834155177646089729741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72956556103451764059819827 109434834155177646089729741)
              ·
                refine ⟨41038062808191617283648653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109434834155177646089729741 41038062808191617283648653)
                ·
                  refine ⟨15389273553071856481368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41038062808191617283648653 15389273553071856481368245)
                  ·
                    refine ⟨1442744395600486545128273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15389273553071856481368245 1442744395600486545128273)
                    ·
                      refine ⟨1082058296700364908846205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442744395600486545128273 1082058296700364908846205)
                      ·
                        rfl

theorem cell23_2107301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_2107301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107301 prefixEnd_2107301 := by exact prefixLift 2107301
  have htrace : WordTrace (prefixWord ++ tailWord_2107301) baseStart_2107301 baseEnd_2107301 := by
    simpa [prefixWord, tailWord_2107301, baseEnd_2107301] using wordTrace_append hprefix tailTrace_2107301
  have hstable : (prefixWord ++ tailWord_2107301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107301).length < 2 ^ (prefixWord ++ tailWord_2107301).sum := by decide
  have hdescent : baseEnd_2107301 < baseStart_2107301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107328 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 1, 5]
def baseStart_2107328 : Nat := 118140960795 + 2107328 * 2 ^ 59
def prefixEnd_2107328 : Nat := 4983230072969 + 3 ^ 40 * 2107328 * 2
def baseEnd_2107328 : Nat := 360690720226012101069527

theorem tailTrace_2107328 : CollatzResearch.WordTrace tailWord_2107328 prefixEnd_2107328 360690720226012101069527 := by
  unfold tailWord_2107328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38430283254759016907085319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51240377673012022542780425 38430283254759016907085319)
  ·
    refine ⟨57645424882138525360627979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38430283254759016907085319 57645424882138525360627979)
    ·
      refine ⟨86468137323207788040941969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57645424882138525360627979 86468137323207788040941969)
      ·
        refine ⟨64851102992405841030706477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86468137323207788040941969 64851102992405841030706477)
        ·
          refine ⟨24319163622152190386514929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64851102992405841030706477 24319163622152190386514929)
          ·
            refine ⟨18239372716614142789886197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24319163622152190386514929 18239372716614142789886197)
            ·
              refine ⟨1709941192182575886551831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18239372716614142789886197 1709941192182575886551831)
              ·
                refine ⟨2564911788273863829827747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709941192182575886551831 2564911788273863829827747)
                ·
                  refine ⟨3847367682410795744741621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564911788273863829827747 3847367682410795744741621)
                  ·
                    refine ⟨360690720226012101069527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3847367682410795744741621 360690720226012101069527)
                    ·
                      rfl

theorem cell23_2107328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_2107328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107328 prefixEnd_2107328 := by exact prefixLift 2107328
  have htrace : WordTrace (prefixWord ++ tailWord_2107328) baseStart_2107328 baseEnd_2107328 := by
    simpa [prefixWord, tailWord_2107328, baseEnd_2107328] using wordTrace_append hprefix tailTrace_2107328
  have hstable : (prefixWord ++ tailWord_2107328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107328).length < 2 ^ (prefixWord ++ tailWord_2107328).sum := by decide
  have hdescent : baseEnd_2107328 < baseStart_2107328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107344 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_2107344 : Nat := 118140960795 + 2107344 * 2 ^ 59
def prefixEnd_2107344 : Nat := 4983230072969 + 3 ^ 40 * 2107344 * 2
def baseEnd_2107344 : Nat := 1082080376368508240608507

theorem tailTrace_2107344 : CollatzResearch.WordTrace tailWord_2107344 prefixEnd_2107344 1082080376368508240608507 := by
  unfold tailWord_2107344
  simp only [CollatzResearch.WordTrace]
  refine ⟨38430575038730034273376543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51240766718306712364502057 38430575038730034273376543)
  ·
    refine ⟨57645862558095051410064815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38430575038730034273376543 57645862558095051410064815)
    ·
      refine ⟨86468793837142577115097223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57645862558095051410064815 86468793837142577115097223)
      ·
        refine ⟨129703190755713865672645835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86468793837142577115097223 129703190755713865672645835)
        ·
          refine ⟨194554786133570798508968753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129703190755713865672645835 194554786133570798508968753)
          ·
            refine ⟨145916089600178098881726565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194554786133570798508968753 145916089600178098881726565)
            ·
              refine ⟨27359266800033393540323731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145916089600178098881726565 27359266800033393540323731)
              ·
                refine ⟨41038900200050090310485597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27359266800033393540323731 41038900200050090310485597)
                ·
                  refine ⟨15389587575018783866432099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41038900200050090310485597 15389587575018783866432099)
                  ·
                    refine ⟨23084381362528175799648149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15389587575018783866432099 23084381362528175799648149)
                    ·
                      refine ⟨1082080376368508240608507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23084381362528175799648149 1082080376368508240608507)
                      ·
                        rfl

theorem cell23_2107344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_2107344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107344 prefixEnd_2107344 := by exact prefixLift 2107344
  have htrace : WordTrace (prefixWord ++ tailWord_2107344) baseStart_2107344 baseEnd_2107344 := by
    simpa [prefixWord, tailWord_2107344, baseEnd_2107344] using wordTrace_append hprefix tailTrace_2107344
  have hstable : (prefixWord ++ tailWord_2107344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107344).length < 2 ^ (prefixWord ++ tailWord_2107344).sum := by decide
  have hdescent : baseEnd_2107344 < baseStart_2107344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107351 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_2107351 : Nat := 118140960795 + 2107351 * 2 ^ 59
def prefixEnd_2107351 : Nat := 4983230072969 + 3 ^ 40 * 2107351 * 2
def baseEnd_2107351 : Nat := 1082083970733089713220975

theorem tailTrace_2107351 : CollatzResearch.WordTrace tailWord_2107351 prefixEnd_2107351 1082083970733089713220975 := by
  unfold tailWord_2107351
  simp only [CollatzResearch.WordTrace]
  refine ⟨76861405388434708742257907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51240936925623139161505271 76861405388434708742257907)
  ·
    refine ⟨115292108082652063113386861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76861405388434708742257907 115292108082652063113386861)
    ·
      refine ⟨43234540530994523667520073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115292108082652063113386861 43234540530994523667520073)
      ·
        refine ⟨32425905398245892750640055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43234540530994523667520073 32425905398245892750640055)
        ·
          refine ⟨48638858097368839125960083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32425905398245892750640055 48638858097368839125960083)
          ·
            refine ⟨72958287146053258688940125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48638858097368839125960083 72958287146053258688940125)
            ·
              refine ⟨27359357679769972008352547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72958287146053258688940125 27359357679769972008352547)
              ·
                refine ⟨41039036519654958012528821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27359357679769972008352547 41039036519654958012528821)
                ·
                  refine ⟨3847409673717652313674577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41039036519654958012528821 3847409673717652313674577)
                  ·
                    refine ⟨2885557255288239235255933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847409673717652313674577 2885557255288239235255933)
                    ·
                      refine ⟨1082083970733089713220975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2885557255288239235255933 1082083970733089713220975)
                      ·
                        rfl

theorem cell23_2107351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_2107351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107351 prefixEnd_2107351 := by exact prefixLift 2107351
  have htrace : WordTrace (prefixWord ++ tailWord_2107351) baseStart_2107351 baseEnd_2107351 := by
    simpa [prefixWord, tailWord_2107351, baseEnd_2107351] using wordTrace_append hprefix tailTrace_2107351
  have hstable : (prefixWord ++ tailWord_2107351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107351).length < 2 ^ (prefixWord ++ tailWord_2107351).sum := by decide
  have hdescent : baseEnd_2107351 < baseStart_2107351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107361 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_2107361 : Nat := 118140960795 + 2107361 * 2 ^ 59
def prefixEnd_2107361 : Nat := 4983230072969 + 3 ^ 40 * 2107361 * 2
def baseEnd_2107361 : Nat := 1082089105539634674095929

theorem tailTrace_2107361 : CollatzResearch.WordTrace tailWord_2107361 prefixEnd_2107361 1082089105539634674095929 := by
  unfold tailWord_2107361
  simp only [CollatzResearch.WordTrace]
  refine ⟨76861770118398480450121937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51241180078932320300081291 76861770118398480450121937)
  ·
    refine ⟨57646327588798860337591453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76861770118398480450121937 57646327588798860337591453)
    ·
      refine ⟨21617372845799572626596795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57646327588798860337591453 21617372845799572626596795)
      ·
        refine ⟨32426059268699358939895193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21617372845799572626596795 32426059268699358939895193)
        ·
          refine ⟨24319544451524519204921395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32426059268699358939895193 24319544451524519204921395)
          ·
            refine ⟨36479316677286778807382093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24319544451524519204921395 36479316677286778807382093)
            ·
              refine ⟨13679743753982542052768285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36479316677286778807382093 13679743753982542052768285)
              ·
                refine ⟨5129903907743453269788107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13679743753982542052768285 5129903907743453269788107)
                ·
                  refine ⟨7694855861615179904682161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129903907743453269788107 7694855861615179904682161)
                  ·
                    refine ⟨5771141896211384928511621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7694855861615179904682161 5771141896211384928511621)
                    ·
                      refine ⟨1082089105539634674095929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5771141896211384928511621 1082089105539634674095929)
                      ·
                        rfl

theorem cell23_2107361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_2107361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107361 prefixEnd_2107361 := by exact prefixLift 2107361
  have htrace : WordTrace (prefixWord ++ tailWord_2107361) baseStart_2107361 baseEnd_2107361 := by
    simpa [prefixWord, tailWord_2107361, baseEnd_2107361] using wordTrace_append hprefix tailTrace_2107361
  have hstable : (prefixWord ++ tailWord_2107361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107361).length < 2 ^ (prefixWord ++ tailWord_2107361).sum := by decide
  have hdescent : baseEnd_2107361 < baseStart_2107361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107368 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2107368 : Nat := 118140960795 + 2107368 * 2 ^ 59
def prefixEnd_2107368 : Nat := 4983230072969 + 3 ^ 40 * 2107368 * 2
def baseEnd_2107368 : Nat := 1082092699904216146708397

theorem tailTrace_2107368 : CollatzResearch.WordTrace tailWord_2107368 prefixEnd_2107368 1082092699904216146708397 := by
  unfold tailWord_2107368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38431012714686560322813379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51241350286248747097084505 38431012714686560322813379)
  ·
    refine ⟨57646519072029840484220069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38431012714686560322813379 57646519072029840484220069)
    ·
      refine ⟨10808722326005595090791263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57646519072029840484220069 10808722326005595090791263)
      ·
        refine ⟨16213083489008392636186895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10808722326005595090791263 16213083489008392636186895)
        ·
          refine ⟨24319625233512588954280343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16213083489008392636186895 24319625233512588954280343)
          ·
            refine ⟨36479437850268883431420515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24319625233512588954280343 36479437850268883431420515)
            ·
              refine ⟨54719156775403325147130773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36479437850268883431420515 54719156775403325147130773)
              ·
                refine ⟨2564960473847030866271755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54719156775403325147130773 2564960473847030866271755)
                ·
                  refine ⟨3847440710770546299407633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564960473847030866271755 3847440710770546299407633)
                  ·
                    refine ⟨2885580533077909724555725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847440710770546299407633 2885580533077909724555725)
                    ·
                      refine ⟨1082092699904216146708397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2885580533077909724555725 1082092699904216146708397)
                      ·
                        rfl

theorem cell23_2107368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2107368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107368 prefixEnd_2107368 := by exact prefixLift 2107368
  have htrace : WordTrace (prefixWord ++ tailWord_2107368) baseStart_2107368 baseEnd_2107368 := by
    simpa [prefixWord, tailWord_2107368, baseEnd_2107368] using wordTrace_append hprefix tailTrace_2107368
  have hstable : (prefixWord ++ tailWord_2107368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107368).length < 2 ^ (prefixWord ++ tailWord_2107368).sum := by decide
  have hdescent : baseEnd_2107368 < baseStart_2107368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107385 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 1, 2, 3]
def baseStart_2107385 : Nat := 118140960795 + 2107385 * 2 ^ 59
def prefixEnd_2107385 : Nat := 4983230072969 + 3 ^ 40 * 2107385 * 2
def baseEnd_2107385 : Nat := 1082101429075342580195819

theorem tailTrace_2107385 : CollatzResearch.WordTrace tailWord_2107385 prefixEnd_2107385 1082101429075342580195819 := by
  unfold tailWord_2107385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76862645470311532548995609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51241763646874355032663739 76862645470311532548995609)
  ·
    refine ⟨57646984102733649411746707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76862645470311532548995609 57646984102733649411746707)
    ·
      refine ⟨86470476154100474117620061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57646984102733649411746707 86470476154100474117620061)
      ·
        refine ⟨32426428557787677794107523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86470476154100474117620061 32426428557787677794107523)
        ·
          refine ⟨48639642836681516691161285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32426428557787677794107523 48639642836681516691161285)
          ·
            refine ⟨9119933031877784379592741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48639642836681516691161285 9119933031877784379592741)
            ·
              refine ⟨1709987443477084571173639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9119933031877784379592741 1709987443477084571173639)
              ·
                refine ⟨2564981165215626856760459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709987443477084571173639 2564981165215626856760459)
                ·
                  refine ⟨3847471747823440285140689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564981165215626856760459 3847471747823440285140689)
                  ·
                    refine ⟨2885603810867580213855517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847471747823440285140689 2885603810867580213855517)
                    ·
                      refine ⟨1082101429075342580195819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2885603810867580213855517 1082101429075342580195819)
                      ·
                        rfl

theorem cell23_2107385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_2107385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107385 prefixEnd_2107385 := by exact prefixLift 2107385
  have htrace : WordTrace (prefixWord ++ tailWord_2107385) baseStart_2107385 baseEnd_2107385 := by
    simpa [prefixWord, tailWord_2107385, baseEnd_2107385] using wordTrace_append hprefix tailTrace_2107385
  have hstable : (prefixWord ++ tailWord_2107385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107385).length < 2 ^ (prefixWord ++ tailWord_2107385).sum := by decide
  have hdescent : baseEnd_2107385 < baseStart_2107385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107441 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2107441 : Nat := 118140960795 + 2107441 * 2 ^ 59
def prefixEnd_2107441 : Nat := 4983230072969 + 3 ^ 40 * 2107441 * 2
def baseEnd_2107441 : Nat := 1082130183991994361095561

theorem tailTrace_2107441 : CollatzResearch.WordTrace tailWord_2107441 prefixEnd_2107441 1082130183991994361095561 := by
  unfold tailWord_2107441
  simp only [CollatzResearch.WordTrace]
  refine ⟨76864687958108654113034177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51243125305405769408689451 76864687958108654113034177)
  ·
    refine ⟨57648515968581490584775633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76864687958108654113034177 57648515968581490584775633)
    ·
      refine ⟨43236386976436117938581725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57648515968581490584775633 43236386976436117938581725)
      ·
        refine ⟨16213645116163544226968147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43236386976436117938581725 16213645116163544226968147)
        ·
          refine ⟨24320467674245316340452221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16213645116163544226968147 24320467674245316340452221)
          ·
            refine ⟨9120175377841993627669583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24320467674245316340452221 9120175377841993627669583)
            ·
              refine ⟨13680263066762990441504375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120175377841993627669583 13680263066762990441504375)
              ·
                refine ⟨20520394600144485662256563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13680263066762990441504375 20520394600144485662256563)
                ·
                  refine ⟨30780591900216728493384845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20520394600144485662256563 30780591900216728493384845)
                  ·
                    refine ⟨11542721962581273185019317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30780591900216728493384845 11542721962581273185019317)
                    ·
                      refine ⟨1082130183991994361095561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11542721962581273185019317 1082130183991994361095561)
                      ·
                        rfl

theorem cell23_2107441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2107441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107441 prefixEnd_2107441 := by exact prefixLift 2107441
  have htrace : WordTrace (prefixWord ++ tailWord_2107441) baseStart_2107441 baseEnd_2107441 := by
    simpa [prefixWord, tailWord_2107441, baseEnd_2107441] using wordTrace_append hprefix tailTrace_2107441
  have hstable : (prefixWord ++ tailWord_2107441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107441).length < 2 ^ (prefixWord ++ tailWord_2107441).sum := by decide
  have hdescent : baseEnd_2107441 < baseStart_2107441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107455 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 4, 2, 2]
def baseStart_2107455 : Nat := 118140960795 + 2107455 * 2 ^ 59
def prefixEnd_2107455 : Nat := 4983230072969 + 3 ^ 40 * 2107455 * 2
def baseEnd_2107455 : Nat := 1082137372721157306320497

theorem tailTrace_2107455 : CollatzResearch.WordTrace tailWord_2107455 prefixEnd_2107455 1082137372721157306320497 := by
  unfold tailWord_2107455
  simp only [CollatzResearch.WordTrace]
  refine ⟨76865198580057934504043819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51243465720038623002695879 76865198580057934504043819)
  ·
    refine ⟨115297797870086901756065729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76865198580057934504043819 115297797870086901756065729)
    ·
      refine ⟨86473348402565176317049297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115297797870086901756065729 86473348402565176317049297)
      ·
        refine ⟨64855011301923882237786973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86473348402565176317049297 64855011301923882237786973)
        ·
          refine ⟨24320629238221455839170115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64855011301923882237786973 24320629238221455839170115)
          ·
            refine ⟨36480943857332183758755173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24320629238221455839170115 36480943857332183758755173)
            ·
              refine ⟨6840176973249784454766595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36480943857332183758755173 6840176973249784454766595)
              ·
                refine ⟨10260265459874676682149893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840176973249784454766595 10260265459874676682149893)
                ·
                  refine ⟨1923799773726501877903105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10260265459874676682149893 1923799773726501877903105)
                  ·
                    refine ⟨1442849830294876408427329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1923799773726501877903105 1442849830294876408427329)
                    ·
                      refine ⟨1082137372721157306320497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1442849830294876408427329 1082137372721157306320497)
                      ·
                        rfl

theorem cell23_2107455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_2107455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107455 prefixEnd_2107455 := by exact prefixLift 2107455
  have htrace : WordTrace (prefixWord ++ tailWord_2107455) baseStart_2107455 baseEnd_2107455 := by
    simpa [prefixWord, tailWord_2107455, baseEnd_2107455] using wordTrace_append hprefix tailTrace_2107455
  have hstable : (prefixWord ++ tailWord_2107455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107455).length < 2 ^ (prefixWord ++ tailWord_2107455).sum := by decide
  have hdescent : baseEnd_2107455 < baseStart_2107455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107491 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 7]
def baseStart_2107491 : Nat := 118140960795 + 2107491 * 2 ^ 59
def prefixEnd_2107491 : Nat := 4983230072969 + 3 ^ 40 * 2107491 * 2
def baseEnd_2107491 : Nat := 360718619341573055156777

theorem tailTrace_2107491 : CollatzResearch.WordTrace tailWord_2107491 prefixEnd_2107491 360718619341573055156777 := by
  unfold tailWord_2107491
  simp only [CollatzResearch.WordTrace]
  refine ⟨76866511607927512652354327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51244341071951675101569551 76866511607927512652354327)
  ·
    refine ⟨115299767411891268978531491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76866511607927512652354327 115299767411891268978531491)
    ·
      refine ⟨172949651117836903467797237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115299767411891268978531491 172949651117836903467797237)
      ·
        refine ⟨16214029792297209700105991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172949651117836903467797237 16214029792297209700105991)
        ·
          refine ⟨24321044688445814550158987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16214029792297209700105991 24321044688445814550158987)
          ·
            refine ⟨36481567032668721825238481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24321044688445814550158987 36481567032668721825238481)
            ·
              refine ⟨27361175274501541368928861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36481567032668721825238481 27361175274501541368928861)
              ·
                refine ⟨10260440727938078013348323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27361175274501541368928861 10260440727938078013348323)
                ·
                  refine ⟨15390661091907117020022485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10260440727938078013348323 15390661091907117020022485)
                  ·
                    refine ⟨360718619341573055156777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15390661091907117020022485 360718619341573055156777)
                    ·
                      rfl

theorem cell23_2107491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_2107491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107491 prefixEnd_2107491 := by exact prefixLift 2107491
  have htrace : WordTrace (prefixWord ++ tailWord_2107491) baseStart_2107491 baseEnd_2107491 := by
    simpa [prefixWord, tailWord_2107491, baseEnd_2107491] using wordTrace_append hprefix tailTrace_2107491
  have hstable : (prefixWord ++ tailWord_2107491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107491).length < 2 ^ (prefixWord ++ tailWord_2107491).sum := by decide
  have hdescent : baseEnd_2107491 < baseStart_2107491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107595 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 3]
def baseStart_2107595 : Nat := 118140960795 + 2107595 * 2 ^ 59
def prefixEnd_2107595 : Nat := 4983230072969 + 3 ^ 40 * 2107595 * 2
def baseEnd_2107595 : Nat := 1082209260012786758569853

theorem tailTrace_2107595 : CollatzResearch.WordTrace tailWord_2107595 prefixEnd_2107595 1082209260012786758569853 := by
  unfold tailWord_2107595
  simp only [CollatzResearch.WordTrace]
  refine ⟨76870304799550738414140239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51246869866367158942760159 76870304799550738414140239)
  ·
    refine ⟨115305457199326107621210359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76870304799550738414140239 115305457199326107621210359)
    ·
      refine ⟨172958185798989161431815539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115305457199326107621210359 172958185798989161431815539)
      ·
        refine ⟨259437278698483742147723309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172958185798989161431815539 259437278698483742147723309)
        ·
          refine ⟨97288979511931403305396241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259437278698483742147723309 97288979511931403305396241)
          ·
            refine ⟨72966734633948552479047181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97288979511931403305396241 72966734633948552479047181)
            ·
              refine ⟨27362525487730707179642693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72966734633948552479047181 27362525487730707179642693)
              ·
                refine ⟨5130473528949507596183005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27362525487730707179642693 5130473528949507596183005)
                ·
                  refine ⟨1923927573356065348568627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5130473528949507596183005 1923927573356065348568627)
                  ·
                    refine ⟨2885891360034098022852941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1923927573356065348568627 2885891360034098022852941)
                    ·
                      refine ⟨1082209260012786758569853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2885891360034098022852941 1082209260012786758569853)
                      ·
                        rfl

theorem cell23_2107595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 1, 3].length) (baseStart_2107595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107595 prefixEnd_2107595 := by exact prefixLift 2107595
  have htrace : WordTrace (prefixWord ++ tailWord_2107595) baseStart_2107595 baseEnd_2107595 := by
    simpa [prefixWord, tailWord_2107595, baseEnd_2107595] using wordTrace_append hprefix tailTrace_2107595
  have hstable : (prefixWord ++ tailWord_2107595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107595).length < 2 ^ (prefixWord ++ tailWord_2107595).sum := by decide
  have hdescent : baseEnd_2107595 < baseStart_2107595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107606 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2107606 : Nat := 118140960795 + 2107606 * 2 ^ 59
def prefixEnd_2107606 : Nat := 4983230072969 + 3 ^ 40 * 2107606 * 2
def baseEnd_2107606 : Nat := 360738302766662071844101

theorem tailTrace_2107606 : CollatzResearch.WordTrace tailWord_2107606 prefixEnd_2107606 360738302766662071844101 := by
  unfold tailWord_2107606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804419125156930455799417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51247137335007258195193781 4804419125156930455799417)
  ·
    refine ⟨3603314343867697841849563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4804419125156930455799417 3603314343867697841849563)
    ·
      refine ⟨5404971515801546762774345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603314343867697841849563 5404971515801546762774345)
      ·
        refine ⟨4053728636851160072080759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5404971515801546762774345 4053728636851160072080759)
        ·
          refine ⟨6080592955276740108121139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053728636851160072080759 6080592955276740108121139)
          ·
            refine ⟨9120889432915110162181709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080592955276740108121139 9120889432915110162181709)
            ·
              refine ⟨3420333537343166310818141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9120889432915110162181709 3420333537343166310818141)
              ·
                refine ⟨1282625076503687366556803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3420333537343166310818141 1282625076503687366556803)
                ·
                  refine ⟨1923937614755531049835205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282625076503687366556803 1923937614755531049835205)
                  ·
                    refine ⟨360738302766662071844101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923937614755531049835205 360738302766662071844101)
                    ·
                      rfl

theorem cell23_2107606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2107606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107606 prefixEnd_2107606 := by exact prefixLift 2107606
  have htrace : WordTrace (prefixWord ++ tailWord_2107606) baseStart_2107606 baseEnd_2107606 := by
    simpa [prefixWord, tailWord_2107606, baseEnd_2107606] using wordTrace_append hprefix tailTrace_2107606
  have hstable : (prefixWord ++ tailWord_2107606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107606).length < 2 ^ (prefixWord ++ tailWord_2107606).sum := by decide
  have hdescent : baseEnd_2107606 < baseStart_2107606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107648 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_2107648 : Nat := 118140960795 + 2107648 * 2 ^ 59
def prefixEnd_2107648 : Nat := 4983230072969 + 3 ^ 40 * 2107648 * 2
def baseEnd_2107648 : Nat := 1082236474487475051207109

theorem tailTrace_2107648 : CollatzResearch.WordTrace tailWord_2107648 prefixEnd_2107648 1082236474487475051207109 := by
  unfold tailWord_2107648
  simp only [CollatzResearch.WordTrace]
  refine ⟨38436118934179364232909799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51248158578905818977213065 38436118934179364232909799)
  ·
    refine ⟨57654178401269046349364699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38436118934179364232909799 57654178401269046349364699)
    ·
      refine ⟨86481267601903569524047049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57654178401269046349364699 86481267601903569524047049)
      ·
        refine ⟨64860950701427677143035287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86481267601903569524047049 64860950701427677143035287)
        ·
          refine ⟨97291426052141515714552931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64860950701427677143035287 97291426052141515714552931)
          ·
            refine ⟨145937139078212273571829397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97291426052141515714552931 145937139078212273571829397)
            ·
              refine ⟨6840803394291200323679503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145937139078212273571829397 6840803394291200323679503)
              ·
                refine ⟨10261205091436800485519255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840803394291200323679503 10261205091436800485519255)
                ·
                  refine ⟨15391807637155200728278883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10261205091436800485519255 15391807637155200728278883)
                  ·
                    refine ⟨23087711455732801092418325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15391807637155200728278883 23087711455732801092418325)
                    ·
                      refine ⟨1082236474487475051207109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23087711455732801092418325 1082236474487475051207109)
                      ·
                        rfl

theorem cell23_2107648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_2107648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107648 prefixEnd_2107648 := by exact prefixLift 2107648
  have htrace : WordTrace (prefixWord ++ tailWord_2107648) baseStart_2107648 baseEnd_2107648 := by
    simpa [prefixWord, tailWord_2107648, baseEnd_2107648] using wordTrace_append hprefix tailTrace_2107648
  have hstable : (prefixWord ++ tailWord_2107648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107648).length < 2 ^ (prefixWord ++ tailWord_2107648).sum := by decide
  have hdescent : baseEnd_2107648 < baseStart_2107648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107652 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2107652 : Nat := 118140960795 + 2107652 * 2 ^ 59
def prefixEnd_2107652 : Nat := 4983230072969 + 3 ^ 40 * 2107652 * 2
def baseEnd_2107652 : Nat := 1082238528410093035557091

theorem tailTrace_2107652 : CollatzResearch.WordTrace tailWord_2107652 prefixEnd_2107652 1082238528410093035557091 := by
  unfold tailWord_2107652
  simp only [CollatzResearch.WordTrace]
  refine ⟨38436191880172118574482605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51248255840229491432643473 38436191880172118574482605)
  ·
    refine ⟨14413571955064544465430977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38436191880172118574482605 14413571955064544465430977)
    ·
      refine ⟨10810178966298408349073233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14413571955064544465430977 10810178966298408349073233)
      ·
        refine ⟨8107634224723806261804925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10810178966298408349073233 8107634224723806261804925)
        ·
          refine ⟨3040362834271427348176847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8107634224723806261804925 3040362834271427348176847)
          ·
            refine ⟨4560544251407141022265271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040362834271427348176847 4560544251407141022265271)
            ·
              refine ⟨6840816377110711533397907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560544251407141022265271 6840816377110711533397907)
              ·
                refine ⟨10261224565666067300096861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840816377110711533397907 10261224565666067300096861)
                ·
                  refine ⟨3847959212124775237536323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10261224565666067300096861 3847959212124775237536323)
                  ·
                    refine ⟨5771938818187162856304485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3847959212124775237536323 5771938818187162856304485)
                    ·
                      refine ⟨1082238528410093035557091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5771938818187162856304485 1082238528410093035557091)
                      ·
                        rfl

theorem cell23_2107652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2107652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107652 prefixEnd_2107652 := by exact prefixLift 2107652
  have htrace : WordTrace (prefixWord ++ tailWord_2107652) baseStart_2107652 baseEnd_2107652 := by
    simpa [prefixWord, tailWord_2107652, baseEnd_2107652] using wordTrace_append hprefix tailTrace_2107652
  have hstable : (prefixWord ++ tailWord_2107652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107652).length < 2 ^ (prefixWord ++ tailWord_2107652).sum := by decide
  have hdescent : baseEnd_2107652 < baseStart_2107652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107658 : List Nat := [3, 1, 2, 2, 1, 1, 4, 9]
def baseStart_2107658 : Nat := 118140960795 + 2107658 * 2 ^ 59
def prefixEnd_2107658 : Nat := 4983230072969 + 3 ^ 40 * 2107658 * 2
def baseEnd_2107658 : Nat := 40083022566445185632669

theorem tailTrace_2107658 : CollatzResearch.WordTrace tailWord_2107658 prefixEnd_2107658 40083022566445185632669 := by
  unfold tailWord_2107658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19218150649580625043420907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51248401732215000115789085 19218150649580625043420907)
  ·
    refine ⟨28827225974370937565131361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19218150649580625043420907 28827225974370937565131361)
    ·
      refine ⟨21620419480778203173848521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28827225974370937565131361 21620419480778203173848521)
      ·
        refine ⟨16215314610583652380386391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21620419480778203173848521 16215314610583652380386391)
        ·
          refine ⟨24322971915875478570579587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16215314610583652380386391 24322971915875478570579587)
          ·
            refine ⟨36484457873813217855869381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24322971915875478570579587 36484457873813217855869381)
            ·
              refine ⟨6840835851339978347975509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36484457873813217855869381 6840835851339978347975509)
              ·
                refine ⟨40083022566445185632669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6840835851339978347975509 40083022566445185632669)
                ·
                  rfl

theorem cell23_2107658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_2107658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107658 prefixEnd_2107658 := by exact prefixLift 2107658
  have htrace : WordTrace (prefixWord ++ tailWord_2107658) baseStart_2107658 baseEnd_2107658 := by
    simpa [prefixWord, tailWord_2107658, baseEnd_2107658] using wordTrace_append hprefix tailTrace_2107658
  have hstable : (prefixWord ++ tailWord_2107658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107658).length < 2 ^ (prefixWord ++ tailWord_2107658).sum := by decide
  have hdescent : baseEnd_2107658 < baseStart_2107658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107665 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_2107665 : Nat := 118140960795 + 2107665 * 2 ^ 59
def prefixEnd_2107665 : Nat := 4983230072969 + 3 ^ 40 * 2107665 * 2
def baseEnd_2107665 : Nat := 1082245203658601484694531

theorem tailTrace_2107665 : CollatzResearch.WordTrace tailWord_2107665 prefixEnd_2107665 1082245203658601484694531 := by
  unfold tailWord_2107665
  simp only [CollatzResearch.WordTrace]
  refine ⟨76872857909297140369188449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51248571939531426912792299 76872857909297140369188449)
  ·
    refine ⟨57654643431972855276891337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76872857909297140369188449 57654643431972855276891337)
    ·
      refine ⟨43240982573979641457668503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57654643431972855276891337 43240982573979641457668503)
      ·
        refine ⟨64861473860969462186502755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43240982573979641457668503 64861473860969462186502755)
        ·
          refine ⟨97292210791454193279754133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64861473860969462186502755 97292210791454193279754133)
          ·
            refine ⟨4560572380849415309988475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97292210791454193279754133 4560572380849415309988475)
            ·
              refine ⟨6840858571274122964982713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560572380849415309988475 6840858571274122964982713)
              ·
                refine ⟨5130643928455592223737035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6840858571274122964982713 5130643928455592223737035)
                ·
                  refine ⟨7695965892683388335605553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130643928455592223737035 7695965892683388335605553)
                  ·
                    refine ⟨5771974419512541251704165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7695965892683388335605553 5771974419512541251704165)
                    ·
                      refine ⟨1082245203658601484694531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5771974419512541251704165 1082245203658601484694531)
                      ·
                        rfl

theorem cell23_2107665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_2107665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107665 prefixEnd_2107665 := by exact prefixLift 2107665
  have htrace : WordTrace (prefixWord ++ tailWord_2107665) baseStart_2107665 baseEnd_2107665 := by
    simpa [prefixWord, tailWord_2107665, baseEnd_2107665] using wordTrace_append hprefix tailTrace_2107665
  have hstable : (prefixWord ++ tailWord_2107665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107665).length < 2 ^ (prefixWord ++ tailWord_2107665).sum := by decide
  have hdescent : baseEnd_2107665 < baseStart_2107665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107729 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_2107729 : Nat := 118140960795 + 2107729 * 2 ^ 59
def prefixEnd_2107729 : Nat := 4983230072969 + 3 ^ 40 * 2107729 * 2
def baseEnd_2107729 : Nat := 1082278066420489234294237

theorem tailTrace_2107729 : CollatzResearch.WordTrace tailWord_2107729 prefixEnd_2107729 1082278066420489234294237 := by
  unfold tailWord_2107729
  simp only [CollatzResearch.WordTrace]
  refine ⟨76875192181065279299518241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51250128120710186199678827 76875192181065279299518241)
  ·
    refine ⟨57656394135798959474638681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76875192181065279299518241 57656394135798959474638681)
    ·
      refine ⟨43242295601849219605979011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57656394135798959474638681 43242295601849219605979011)
      ·
        refine ⟨64863443402773829408968517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43242295601849219605979011 64863443402773829408968517)
        ·
          refine ⟨12161895638020093014181597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64863443402773829408968517 12161895638020093014181597)
          ·
            refine ⟨4560710864257534880318099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12161895638020093014181597 4560710864257534880318099)
            ·
              refine ⟨6841066296386302320477149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560710864257534880318099 6841066296386302320477149)
              ·
                refine ⟨2565399861144863370178931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6841066296386302320477149 2565399861144863370178931)
                ·
                  refine ⟨3848099791717295055268397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565399861144863370178931 3848099791717295055268397)
                  ·
                    refine ⟨1443037421893985645725649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3848099791717295055268397 1443037421893985645725649)
                    ·
                      refine ⟨1082278066420489234294237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443037421893985645725649 1082278066420489234294237)
                      ·
                        rfl

theorem cell23_2107729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_2107729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107729 prefixEnd_2107729 := by exact prefixLift 2107729
  have htrace : WordTrace (prefixWord ++ tailWord_2107729) baseStart_2107729 baseEnd_2107729 := by
    simpa [prefixWord, tailWord_2107729, baseEnd_2107729] using wordTrace_append hprefix tailTrace_2107729
  have hstable : (prefixWord ++ tailWord_2107729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107729).length < 2 ^ (prefixWord ++ tailWord_2107729).sum := by decide
  have hdescent : baseEnd_2107729 < baseStart_2107729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107829 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2107829 : Nat := 118140960795 + 2107829 * 2 ^ 59
def prefixEnd_2107829 : Nat := 4983230072969 + 3 ^ 40 * 2107829 * 2
def baseEnd_2107829 : Nat := 360776471495312947681259

theorem tailTrace_2107829 : CollatzResearch.WordTrace tailWord_2107829 prefixEnd_2107829 360776471495312947681259 := by
  unfold tailWord_2107829
  simp only [CollatzResearch.WordTrace]
  refine ⟨76878839480702996378158541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51252559653801997585439027 76878839480702996378158541)
  ·
    refine ⟨28829564805263623641809453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76878839480702996378158541 28829564805263623641809453)
    ·
      refine ⟨10811086801973858865678545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28829564805263623641809453 10811086801973858865678545)
      ·
        refine ⟨8108315101480394149258909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10811086801973858865678545 8108315101480394149258909)
        ·
          refine ⟨3040618163055147805972091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8108315101480394149258909 3040618163055147805972091)
          ·
            refine ⟨4560927244582721708958137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040618163055147805972091 4560927244582721708958137)
            ·
              refine ⟨3420695433437041281718603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4560927244582721708958137 3420695433437041281718603)
              ·
                refine ⟨5131043150155561922577905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420695433437041281718603 5131043150155561922577905)
                ·
                  refine ⟨3848282362616671441933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131043150155561922577905 3848282362616671441933429)
                  ·
                    refine ⟨360776471495312947681259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3848282362616671441933429 360776471495312947681259)
                    ·
                      rfl

theorem cell23_2107829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2107829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107829 prefixEnd_2107829 := by exact prefixLift 2107829
  have htrace : WordTrace (prefixWord ++ tailWord_2107829) baseStart_2107829 baseEnd_2107829 := by
    simpa [prefixWord, tailWord_2107829, baseEnd_2107829] using wordTrace_append hprefix tailTrace_2107829
  have hstable : (prefixWord ++ tailWord_2107829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107829).length < 2 ^ (prefixWord ++ tailWord_2107829).sum := by decide
  have hdescent : baseEnd_2107829 < baseStart_2107829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107832 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_2107832 : Nat := 118140960795 + 2107832 * 2 ^ 59
def prefixEnd_2107832 : Nat := 4983230072969 + 3 ^ 40 * 2107832 * 2
def baseEnd_2107832 : Nat := 1082330954927902331306263

theorem tailTrace_2107832 : CollatzResearch.WordTrace tailWord_2107832 prefixEnd_2107832 1082330954927902331306263 := by
  unfold tailWord_2107832
  simp only [CollatzResearch.WordTrace]
  refine ⟨38439474449846063945258875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51252632599794751927011833 38439474449846063945258875)
  ·
    refine ⟨57659211674769095917888313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38439474449846063945258875 57659211674769095917888313)
    ·
      refine ⟨43244408756076821938416235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57659211674769095917888313 43244408756076821938416235)
      ·
        refine ⟨64866613134115232907624353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43244408756076821938416235 64866613134115232907624353)
        ·
          refine ⟨48649959850586424680718265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64866613134115232907624353 48649959850586424680718265)
          ·
            refine ⟨36487469887939818510538699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48649959850586424680718265 36487469887939818510538699)
            ·
              refine ⟨54731204831909727765808049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36487469887939818510538699 54731204831909727765808049)
              ·
                refine ⟨41048403623932295824356037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54731204831909727765808049 41048403623932295824356037)
                ·
                  refine ⟨7696575679487305467066757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41048403623932295824356037 7696575679487305467066757)
                  ·
                    refine ⟨1443107939903869775075017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7696575679487305467066757 1443107939903869775075017)
                    ·
                      refine ⟨1082330954927902331306263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443107939903869775075017 1082330954927902331306263)
                      ·
                        rfl

theorem cell23_2107832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_2107832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107832 prefixEnd_2107832 := by exact prefixLift 2107832
  have htrace : WordTrace (prefixWord ++ tailWord_2107832) baseStart_2107832 baseEnd_2107832 := by
    simpa [prefixWord, tailWord_2107832, baseEnd_2107832] using wordTrace_append hprefix tailTrace_2107832
  have hstable : (prefixWord ++ tailWord_2107832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107832).length < 2 ^ (prefixWord ++ tailWord_2107832).sum := by decide
  have hdescent : baseEnd_2107832 < baseStart_2107832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107886 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2107886 : Nat := 118140960795 + 2107886 * 2 ^ 59
def prefixEnd_2107886 : Nat := 4983230072969 + 3 ^ 40 * 2107886 * 2
def baseEnd_2107886 : Nat := 1082358682883245120031015

theorem tailTrace_2107886 : CollatzResearch.WordTrace tailWord_2107886 prefixEnd_2107886 1082358682883245120031015 := by
  unfold tailWord_2107886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610114805187061889122939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51253945627664330075322341 9610114805187061889122939)
  ·
    refine ⟨14415172207780592833684409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9610114805187061889122939 14415172207780592833684409)
    ·
      refine ⟨10811379155835444625263307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14415172207780592833684409 10811379155835444625263307)
      ·
        refine ⟨16217068733753166937894961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10811379155835444625263307 16217068733753166937894961)
        ·
          refine ⟨12162801550314875203421221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16217068733753166937894961 12162801550314875203421221)
          ·
            refine ⟨2280525290684039100641479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12162801550314875203421221 2280525290684039100641479)
            ·
              refine ⟨3420787936026058650962219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280525290684039100641479 3420787936026058650962219)
              ·
                refine ⟨5131181904039087976443329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420787936026058650962219 5131181904039087976443329)
                ·
                  refine ⟨3848386428029315982332497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131181904039087976443329 3848386428029315982332497)
                  ·
                    refine ⟨2886289821021986986749373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3848386428029315982332497 2886289821021986986749373)
                    ·
                      refine ⟨1082358682883245120031015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886289821021986986749373 1082358682883245120031015)
                      ·
                        rfl

theorem cell23_2107886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2107886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107886 prefixEnd_2107886 := by exact prefixLift 2107886
  have htrace : WordTrace (prefixWord ++ tailWord_2107886) baseStart_2107886 baseEnd_2107886 := by
    simpa [prefixWord, tailWord_2107886, baseEnd_2107886] using wordTrace_append hprefix tailTrace_2107886
  have hstable : (prefixWord ++ tailWord_2107886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107886).length < 2 ^ (prefixWord ++ tailWord_2107886).sum := by decide
  have hdescent : baseEnd_2107886 < baseStart_2107886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107909 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_2107909 : Nat := 118140960795 + 2107909 * 2 ^ 59
def prefixEnd_2107909 : Nat := 4983230072969 + 3 ^ 40 * 2107909 * 2
def baseEnd_2107909 : Nat := 1082370492938298530043409

theorem tailTrace_2107909 : CollatzResearch.WordTrace tailWord_2107909 prefixEnd_2107909 1082370492938298530043409 := by
  unfold tailWord_2107909
  simp only [CollatzResearch.WordTrace]
  refine ⟨76881757320413170041070781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51254504880275446694047187 76881757320413170041070781)
  ·
    refine ⟨28830658995154938765401543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76881757320413170041070781 28830658995154938765401543)
    ·
      refine ⟨43245988492732408148102315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28830658995154938765401543 43245988492732408148102315)
      ·
        refine ⟨64868982739098612222153473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43245988492732408148102315 64868982739098612222153473)
        ·
          refine ⟨48651737054323959166615105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64868982739098612222153473 48651737054323959166615105)
          ·
            refine ⟨36488802790742969374961329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48651737054323959166615105 36488802790742969374961329)
            ·
              refine ⟨27366602093057227031220997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36488802790742969374961329 27366602093057227031220997)
              ·
                refine ⟨5131237892448230068353937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27366602093057227031220997 5131237892448230068353937)
                ·
                  refine ⟨3848428419336172551265453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131237892448230068353937 3848428419336172551265453)
                  ·
                    refine ⟨1443160657251064706724545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3848428419336172551265453 1443160657251064706724545)
                    ·
                      refine ⟨1082370492938298530043409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443160657251064706724545 1082370492938298530043409)
                      ·
                        rfl

theorem cell23_2107909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_2107909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107909 prefixEnd_2107909 := by exact prefixLift 2107909
  have htrace : WordTrace (prefixWord ++ tailWord_2107909) baseStart_2107909 baseEnd_2107909 := by
    simpa [prefixWord, tailWord_2107909, baseEnd_2107909] using wordTrace_append hprefix tailTrace_2107909
  have hstable : (prefixWord ++ tailWord_2107909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107909).length < 2 ^ (prefixWord ++ tailWord_2107909).sum := by decide
  have hdescent : baseEnd_2107909 < baseStart_2107909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107910 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2107910 : Nat := 118140960795 + 2107910 * 2 ^ 59
def prefixEnd_2107910 : Nat := 4983230072969 + 3 ^ 40 * 2107910 * 2
def baseEnd_2107910 : Nat := 360790335472984342043635

theorem tailTrace_2107910 : CollatzResearch.WordTrace tailWord_2107910 prefixEnd_2107910 360790335472984342043635 := by
  unfold tailWord_2107910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402556056044048350370537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51254529195606364807904789 2402556056044048350370537)
  ·
    refine ⟨1801917042033036262777903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2402556056044048350370537 1801917042033036262777903)
    ·
      refine ⟨2702875563049554394166855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801917042033036262777903 2702875563049554394166855)
      ·
        refine ⟨4054313344574331591250283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702875563049554394166855 4054313344574331591250283)
        ·
          refine ⟨6081470016861497386875425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054313344574331591250283 6081470016861497386875425)
          ·
            refine ⟨4561102512646123040156569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6081470016861497386875425 4561102512646123040156569)
            ·
              refine ⟨3420826884484592280117427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561102512646123040156569 3420826884484592280117427)
              ·
                refine ⟨5131240326726888420176141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420826884484592280117427 5131240326726888420176141)
                ·
                  refine ⟨1924215122522583157566053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5131240326726888420176141 1924215122522583157566053)
                  ·
                    refine ⟨360790335472984342043635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1924215122522583157566053 360790335472984342043635)
                    ·
                      rfl

theorem cell23_2107910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2107910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107910 prefixEnd_2107910 := by exact prefixLift 2107910
  have htrace : WordTrace (prefixWord ++ tailWord_2107910) baseStart_2107910 baseEnd_2107910 := by
    simpa [prefixWord, tailWord_2107910, baseEnd_2107910] using wordTrace_append hprefix tailTrace_2107910
  have hstable : (prefixWord ++ tailWord_2107910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107910).length < 2 ^ (prefixWord ++ tailWord_2107910).sum := by decide
  have hdescent : baseEnd_2107910 < baseStart_2107910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107916 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_2107916 : Nat := 118140960795 + 2107916 * 2 ^ 59
def prefixEnd_2107916 : Nat := 4983230072969 + 3 ^ 40 * 2107916 * 2
def baseEnd_2107916 : Nat := 1082374087302880002655877

theorem tailTrace_2107916 : CollatzResearch.WordTrace tailWord_2107916 prefixEnd_2107916 1082374087302880002655877 := by
  unfold tailWord_2107916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38441006315693905118287801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51254675087591873491050401 38441006315693905118287801)
  ·
    refine ⟨28830754736770428838715851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38441006315693905118287801 28830754736770428838715851)
    ·
      refine ⟨43246132105155643258073777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28830754736770428838715851 43246132105155643258073777)
      ·
        refine ⟨32434599078866732443555333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43246132105155643258073777 32434599078866732443555333)
        ·
          refine ⟨6081487327287512333166625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32434599078866732443555333 6081487327287512333166625)
          ·
            refine ⟨4561115495465634249874969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6081487327287512333166625 4561115495465634249874969)
            ·
              refine ⟨3420836621599225687406227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561115495465634249874969 3420836621599225687406227)
              ·
                refine ⟨5131254932398838531109341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420836621599225687406227 5131254932398838531109341)
                ·
                  refine ⟨1924220599649564449166003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5131254932398838531109341 1924220599649564449166003)
                  ·
                    refine ⟨2886330899474346673749005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1924220599649564449166003 2886330899474346673749005)
                    ·
                      refine ⟨1082374087302880002655877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886330899474346673749005 1082374087302880002655877)
                      ·
                        rfl

theorem cell23_2107916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_2107916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107916 prefixEnd_2107916 := by exact prefixLift 2107916
  have htrace : WordTrace (prefixWord ++ tailWord_2107916) baseStart_2107916 baseEnd_2107916 := by
    simpa [prefixWord, tailWord_2107916, baseEnd_2107916] using wordTrace_append hprefix tailTrace_2107916
  have hstable : (prefixWord ++ tailWord_2107916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107916).length < 2 ^ (prefixWord ++ tailWord_2107916).sum := by decide
  have hdescent : baseEnd_2107916 < baseStart_2107916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107936 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_2107936 : Nat := 118140960795 + 2107936 * 2 ^ 59
def prefixEnd_2107936 : Nat := 4983230072969 + 3 ^ 40 * 2107936 * 2
def baseEnd_2107936 : Nat := 360794785638656641468595

theorem tailTrace_2107936 : CollatzResearch.WordTrace tailWord_2107936 prefixEnd_2107936 360794785638656641468595 := by
  unfold tailWord_2107936
  simp only [CollatzResearch.WordTrace]
  refine ⟨38441371045657676826151831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51255161394210235768202441 38441371045657676826151831)
  ·
    refine ⟨57662056568486515239227747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38441371045657676826151831 57662056568486515239227747)
    ·
      refine ⟨86493084852729772858841621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57662056568486515239227747 86493084852729772858841621)
      ·
        refine ⟨4054363352471708102758201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86493084852729772858841621 4054363352471708102758201)
        ·
          refine ⟨3040772514353781077068651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4054363352471708102758201 3040772514353781077068651)
          ·
            refine ⟨4561158771530671615602977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040772514353781077068651 4561158771530671615602977)
            ·
              refine ⟨3420869078648003711702233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561158771530671615602977 3420869078648003711702233)
              ·
                refine ⟨2565651808986002783776675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3420869078648003711702233 2565651808986002783776675)
                ·
                  refine ⟨3848477713479004175665013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565651808986002783776675 3848477713479004175665013)
                  ·
                    refine ⟨360794785638656641468595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3848477713479004175665013 360794785638656641468595)
                    ·
                      rfl

theorem cell23_2107936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_2107936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107936 prefixEnd_2107936 := by exact prefixLift 2107936
  have htrace : WordTrace (prefixWord ++ tailWord_2107936) baseStart_2107936 baseEnd_2107936 := by
    simpa [prefixWord, tailWord_2107936, baseEnd_2107936] using wordTrace_append hprefix tailTrace_2107936
  have hstable : (prefixWord ++ tailWord_2107936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107936).length < 2 ^ (prefixWord ++ tailWord_2107936).sum := by decide
  have hdescent : baseEnd_2107936 < baseStart_2107936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107939 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 4]
def baseStart_2107939 : Nat := 118140960795 + 2107939 * 2 ^ 59
def prefixEnd_2107939 : Nat := 4983230072969 + 3 ^ 40 * 2107939 * 2
def baseEnd_2107939 : Nat := 1082385897357933412668271

theorem tailTrace_2107939 : CollatzResearch.WordTrace tailWord_2107939 prefixEnd_2107939 1082385897357933412668271 := by
  unfold tailWord_2107939
  simp only [CollatzResearch.WordTrace]
  refine ⟨76882851510304485164662871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51255234340202990109775247 76882851510304485164662871)
  ·
    refine ⟨115324277265456727746994307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76882851510304485164662871 115324277265456727746994307)
    ·
      refine ⟨172986415898185091620491461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115324277265456727746994307 172986415898185091620491461)
      ·
        refine ⟨32434952980909704678842149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172986415898185091620491461 32434952980909704678842149)
        ·
          refine ⟨6081553683920569627282903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32434952980909704678842149 6081553683920569627282903)
          ·
            refine ⟨9122330525880854440924355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6081553683920569627282903 9122330525880854440924355)
            ·
              refine ⟨13683495788821281661386533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9122330525880854440924355 13683495788821281661386533)
              ·
                refine ⟨2565655460403990311509975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13683495788821281661386533 2565655460403990311509975)
                ·
                  refine ⟨3848483190605985467264963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565655460403990311509975 3848483190605985467264963)
                  ·
                    refine ⟨5772724785908978200897445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3848483190605985467264963 5772724785908978200897445)
                    ·
                      refine ⟨1082385897357933412668271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5772724785908978200897445 1082385897357933412668271)
                      ·
                        rfl

theorem cell23_2107939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_2107939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107939 prefixEnd_2107939 := by exact prefixLift 2107939
  have htrace : WordTrace (prefixWord ++ tailWord_2107939) baseStart_2107939 baseEnd_2107939 := by
    simpa [prefixWord, tailWord_2107939, baseEnd_2107939] using wordTrace_append hprefix tailTrace_2107939
  have hstable : (prefixWord ++ tailWord_2107939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107939).length < 2 ^ (prefixWord ++ tailWord_2107939).sum := by decide
  have hdescent : baseEnd_2107939 < baseStart_2107939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107952 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_2107952 : Nat := 118140960795 + 2107952 * 2 ^ 59
def prefixEnd_2107952 : Nat := 4983230072969 + 3 ^ 40 * 2107952 * 2
def baseEnd_2107952 : Nat := 1082392572606441861805711

theorem tailTrace_2107952 : CollatzResearch.WordTrace tailWord_2107952 prefixEnd_2107952 1082392572606441861805711 := by
  unfold tailWord_2107952
  simp only [CollatzResearch.WordTrace]
  refine ⟨38441662829628694192443055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51255550439504925589924073 38441662829628694192443055)
  ·
    refine ⟨57662494244443041288664583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38441662829628694192443055 57662494244443041288664583)
    ·
      refine ⟨86493741366664561932996875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57662494244443041288664583 86493741366664561932996875)
      ·
        refine ⟨129740612049996842899495313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86493741366664561932996875 129740612049996842899495313)
        ·
          refine ⟨97305459037497632174621485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129740612049996842899495313 97305459037497632174621485)
          ·
            refine ⟨36489547139061612065483057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97305459037497632174621485 36489547139061612065483057)
            ·
              refine ⟨27367160354296209049112293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36489547139061612065483057 27367160354296209049112293)
              ·
                refine ⟨5131342566430539196708555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27367160354296209049112293 5131342566430539196708555)
                ·
                  refine ⟨7697013849645808795062833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5131342566430539196708555 7697013849645808795062833)
                  ·
                    refine ⟨5772760387234356596297125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7697013849645808795062833 5772760387234356596297125)
                    ·
                      refine ⟨1082392572606441861805711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5772760387234356596297125 1082392572606441861805711)
                      ·
                        rfl

theorem cell23_2107952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_2107952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107952 prefixEnd_2107952 := by exact prefixLift 2107952
  have htrace : WordTrace (prefixWord ++ tailWord_2107952) baseStart_2107952 baseEnd_2107952 := by
    simpa [prefixWord, tailWord_2107952, baseEnd_2107952] using wordTrace_append hprefix tailTrace_2107952
  have hstable : (prefixWord ++ tailWord_2107952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107952).length < 2 ^ (prefixWord ++ tailWord_2107952).sum := by decide
  have hdescent : baseEnd_2107952 < baseStart_2107952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107959 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_2107959 : Nat := 118140960795 + 2107959 * 2 ^ 59
def prefixEnd_2107959 : Nat := 4983230072969 + 3 ^ 40 * 2107959 * 2
def baseEnd_2107959 : Nat := 1082396166971023334418179

theorem tailTrace_2107959 : CollatzResearch.WordTrace tailWord_2107959 prefixEnd_2107959 1082396166971023334418179 := by
  unfold tailWord_2107959
  simp only [CollatzResearch.WordTrace]
  refine ⟨76883580970232028580390931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51255720646821352386927287 76883580970232028580390931)
  ·
    refine ⟨115325371455348042870586397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76883580970232028580390931 115325371455348042870586397)
    ·
      refine ⟨43247014295755516076469899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115325371455348042870586397 43247014295755516076469899)
      ·
        refine ⟨64870521443633274114704849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43247014295755516076469899 64870521443633274114704849)
        ·
          refine ⟨48652891082724955586028637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64870521443633274114704849 48652891082724955586028637)
          ·
            refine ⟨18244834156021858344760739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48652891082724955586028637 18244834156021858344760739)
            ·
              refine ⟨27367251234032787517141109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18244834156021858344760739 27367251234032787517141109)
              ·
                refine ⟨2565679803190573829731979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27367251234032787517141109 2565679803190573829731979)
                ·
                  refine ⟨3848519704785860744597969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565679803190573829731979 3848519704785860744597969)
                  ·
                    refine ⟨2886389778589395558448477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3848519704785860744597969 2886389778589395558448477)
                    ·
                      refine ⟨1082396166971023334418179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886389778589395558448477 1082396166971023334418179)
                      ·
                        rfl

theorem cell23_2107959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_2107959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107959 prefixEnd_2107959 := by exact prefixLift 2107959
  have htrace : WordTrace (prefixWord ++ tailWord_2107959) baseStart_2107959 baseEnd_2107959 := by
    simpa [prefixWord, tailWord_2107959, baseEnd_2107959] using wordTrace_append hprefix tailTrace_2107959
  have hstable : (prefixWord ++ tailWord_2107959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107959).length < 2 ^ (prefixWord ++ tailWord_2107959).sum := by decide
  have hdescent : baseEnd_2107959 < baseStart_2107959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107962 : List Nat := [3, 1, 1, 1, 3, 5, 9]
def baseStart_2107962 : Nat := 118140960795 + 2107962 * 2 ^ 59
def prefixEnd_2107962 : Nat := 4983230072969 + 3 ^ 40 * 2107962 * 2
def baseEnd_2107962 : Nat := 13362934659419590403465

theorem tailTrace_2107962 : CollatzResearch.WordTrace tailWord_2107962 prefixEnd_2107962 13362934659419590403465 := by
  unfold tailWord_2107962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19220922597305290023187535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51255793592814106728500093 19220922597305290023187535)
  ·
    refine ⟨28831383895957935034781303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19220922597305290023187535 28831383895957935034781303)
    ·
      refine ⟨43247075843936902552171955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28831383895957935034781303 43247075843936902552171955)
      ·
        refine ⟨64870613765905353828257933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43247075843936902552171955 64870613765905353828257933)
        ·
          refine ⟨24326480162214507685596725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64870613765905353828257933 24326480162214507685596725)
          ·
            refine ⟨2280607515207610095524693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24326480162214507685596725 2280607515207610095524693)
            ·
              refine ⟨13362934659419590403465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2280607515207610095524693 13362934659419590403465)
              ·
                rfl

theorem cell23_2107962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 9].length) (baseStart_2107962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107962 prefixEnd_2107962 := by exact prefixLift 2107962
  have htrace : WordTrace (prefixWord ++ tailWord_2107962) baseStart_2107962 baseEnd_2107962 := by
    simpa [prefixWord, tailWord_2107962, baseEnd_2107962] using wordTrace_append hprefix tailTrace_2107962
  have hstable : (prefixWord ++ tailWord_2107962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107962).length < 2 ^ (prefixWord ++ tailWord_2107962).sum := by decide
  have hdescent : baseEnd_2107962 < baseStart_2107962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107973 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_2107973 : Nat := 118140960795 + 2107973 * 2 ^ 59
def prefixEnd_2107973 : Nat := 4983230072969 + 3 ^ 40 * 2107973 * 2
def baseEnd_2107973 : Nat := 1082403355700186279643115

theorem tailTrace_2107973 : CollatzResearch.WordTrace tailWord_2107973 prefixEnd_2107973 1082403355700186279643115 := by
  unfold tailWord_2107973
  simp only [CollatzResearch.WordTrace]
  refine ⟨76884091592181308971400573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51256061061454205980933715 76884091592181308971400573)
  ·
    refine ⟨28831534347067990864275215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76884091592181308971400573 28831534347067990864275215)
    ·
      refine ⟨43247301520601986296412823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28831534347067990864275215 43247301520601986296412823)
      ·
        refine ⟨64870952280902979444619235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43247301520601986296412823 64870952280902979444619235)
        ·
          refine ⟨97306428421354469166928853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64870952280902979444619235 97306428421354469166928853)
          ·
            refine ⟨2280619416125495371099895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 97306428421354469166928853 2280619416125495371099895)
            ·
              refine ⟨3420929124188243056649843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280619416125495371099895 3420929124188243056649843)
              ·
                refine ⟨5131393686282364584974765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420929124188243056649843 5131393686282364584974765)
                ·
                  refine ⟨1924272632355886719365537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5131393686282364584974765 1924272632355886719365537)
                  ·
                    refine ⟨1443204474266915039524153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924272632355886719365537 1443204474266915039524153)
                    ·
                      refine ⟨1082403355700186279643115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443204474266915039524153 1082403355700186279643115)
                      ·
                        rfl

theorem cell23_2107973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_2107973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2107973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2107973 prefixEnd_2107973 := by exact prefixLift 2107973
  have htrace : WordTrace (prefixWord ++ tailWord_2107973) baseStart_2107973 baseEnd_2107973 := by
    simpa [prefixWord, tailWord_2107973, baseEnd_2107973] using wordTrace_append hprefix tailTrace_2107973
  have hstable : (prefixWord ++ tailWord_2107973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107973).length < 2 ^ (prefixWord ++ tailWord_2107973).sum := by decide
  have hdescent : baseEnd_2107973 < baseStart_2107973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108074 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2108074 : Nat := 118140960795 + 2108074 * 2 ^ 59
def prefixEnd_2108074 : Nat := 4983230072969 + 3 ^ 40 * 2108074 * 2
def baseEnd_2108074 : Nat := 1082455217246290384480151

theorem tailTrace_2108074 : CollatzResearch.WordTrace tailWord_2108074 prefixEnd_2108074 1082455217246290384480151 := by
  unfold tailWord_2108074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19221943841203850805206819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51258516909876935480551517 19221943841203850805206819)
  ·
    refine ⟨28832915761805776207810229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19221943841203850805206819 28832915761805776207810229)
    ·
      refine ⟨2703085852669291519482209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28832915761805776207810229 2703085852669291519482209)
      ·
        refine ⟨2027314389501968639611657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2703085852669291519482209 2027314389501968639611657)
        ·
          refine ⟨1520485792126476479708743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2027314389501968639611657 1520485792126476479708743)
          ·
            refine ⟨2280728688189714719563115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520485792126476479708743 2280728688189714719563115)
            ·
              refine ⟨3421093032284572079344673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280728688189714719563115 3421093032284572079344673)
              ·
                refine ⟨2565819774213429059508505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421093032284572079344673 2565819774213429059508505)
                ·
                  refine ⟨1924364830660071794631379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565819774213429059508505 1924364830660071794631379)
                  ·
                    refine ⟨2886547245990107691947069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1924364830660071794631379 2886547245990107691947069)
                    ·
                      refine ⟨1082455217246290384480151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886547245990107691947069 1082455217246290384480151)
                      ·
                        rfl

theorem cell23_2108074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2108074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108074 prefixEnd_2108074 := by exact prefixLift 2108074
  have htrace : WordTrace (prefixWord ++ tailWord_2108074) baseStart_2108074 baseEnd_2108074 := by
    simpa [prefixWord, tailWord_2108074, baseEnd_2108074] using wordTrace_append hprefix tailTrace_2108074
  have hstable : (prefixWord ++ tailWord_2108074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108074).length < 2 ^ (prefixWord ++ tailWord_2108074).sum := by decide
  have hdescent : baseEnd_2108074 < baseStart_2108074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108079 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_2108079 : Nat := 118140960795 + 2108079 * 2 ^ 59
def prefixEnd_2108079 : Nat := 4983230072969 + 3 ^ 40 * 2108079 * 2
def baseEnd_2108079 : Nat := 1082457784649562864917627

theorem tailTrace_2108079 : CollatzResearch.WordTrace tailWord_2108079 prefixEnd_2108079 1082457784649562864917627 := by
  unfold tailWord_2108079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76887957729797289074759291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51258638486531526049839527 76887957729797289074759291)
  ·
    refine ⟨115331936594695933612138937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76887957729797289074759291 115331936594695933612138937)
    ·
      refine ⟨86498952446021950209104203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115331936594695933612138937 86498952446021950209104203)
      ·
        refine ⟨129748428669032925313656305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86498952446021950209104203 129748428669032925313656305)
        ·
          refine ⟨97311321501774693985242229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129748428669032925313656305 97311321501774693985242229)
          ·
            refine ⟨9122936390791377561116459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97311321501774693985242229 9122936390791377561116459)
            ·
              refine ⟨13684404586187066341674689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9122936390791377561116459 13684404586187066341674689)
              ·
                refine ⟨10263303439640299756256017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13684404586187066341674689 10263303439640299756256017)
                ·
                  refine ⟨7697477579730224817192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10263303439640299756256017 7697477579730224817192013)
                  ·
                    refine ⟨2886554092398834306447005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7697477579730224817192013 2886554092398834306447005)
                    ·
                      refine ⟨1082457784649562864917627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886554092398834306447005 1082457784649562864917627)
                      ·
                        rfl

theorem cell23_2108079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_2108079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108079 prefixEnd_2108079 := by exact prefixLift 2108079
  have htrace : WordTrace (prefixWord ++ tailWord_2108079) baseStart_2108079 baseEnd_2108079 := by
    simpa [prefixWord, tailWord_2108079, baseEnd_2108079] using wordTrace_append hprefix tailTrace_2108079
  have hstable : (prefixWord ++ tailWord_2108079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108079).length < 2 ^ (prefixWord ++ tailWord_2108079).sum := by decide
  have hdescent : baseEnd_2108079 < baseStart_2108079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108097 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2108097 : Nat := 118140960795 + 2108097 * 2 ^ 59
def prefixEnd_2108097 : Nat := 4983230072969 + 3 ^ 40 * 2108097 * 2
def baseEnd_2108097 : Nat := 1082467027301343794492545

theorem tailTrace_2108097 : CollatzResearch.WordTrace tailWord_2108097 prefixEnd_2108097 1082467027301343794492545 := by
  unfold tailWord_2108097
  simp only [CollatzResearch.WordTrace]
  refine ⟨76888614243732078148914545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51259076162488052099276363 76888614243732078148914545)
  ·
    refine ⟨57666460682799058611685909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76888614243732078148914545 57666460682799058611685909)
    ·
      refine ⟨2703115344506205872422777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57666460682799058611685909 2703115344506205872422777)
      ·
        refine ⟨2027336508379654404317083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2703115344506205872422777 2027336508379654404317083)
        ·
          refine ⟨3041004762569481606475625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027336508379654404317083 3041004762569481606475625)
          ·
            refine ⟨2280753571927111204856719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041004762569481606475625 2280753571927111204856719)
            ·
              refine ⟨3421130357890666807285079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280753571927111204856719 3421130357890666807285079)
              ·
                refine ⟨5131695536836000210927619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421130357890666807285079 5131695536836000210927619)
                ·
                  refine ⟨7697543305254000316391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5131695536836000210927619 7697543305254000316391429)
                  ·
                    refine ⟨1443289369735125059323393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7697543305254000316391429 1443289369735125059323393)
                    ·
                      refine ⟨1082467027301343794492545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443289369735125059323393 1082467027301343794492545)
                      ·
                        rfl

theorem cell23_2108097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2108097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108097 prefixEnd_2108097 := by exact prefixLift 2108097
  have htrace : WordTrace (prefixWord ++ tailWord_2108097) baseStart_2108097 baseEnd_2108097 := by
    simpa [prefixWord, tailWord_2108097, baseEnd_2108097] using wordTrace_append hprefix tailTrace_2108097
  have hstable : (prefixWord ++ tailWord_2108097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108097).length < 2 ^ (prefixWord ++ tailWord_2108097).sum := by decide
  have hdescent : baseEnd_2108097 < baseStart_2108097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108119 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2108119 : Nat := 118140960795 + 2108119 * 2 ^ 59
def prefixEnd_2108119 : Nat := 4983230072969 + 3 ^ 40 * 2108119 * 2
def baseEnd_2108119 : Nat := 1082478323875742708417443

theorem tailTrace_2108119 : CollatzResearch.WordTrace tailWord_2108119 prefixEnd_2108119 1082478323875742708417443 := by
  unfold tailWord_2108119
  simp only [CollatzResearch.WordTrace]
  refine ⟨76889416649652375906215411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51259611099768250604143607 76889416649652375906215411)
  ·
    refine ⟨115334124974478563859323117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76889416649652375906215411 115334124974478563859323117)
    ·
      refine ⟨43250296865429461447246169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115334124974478563859323117 43250296865429461447246169)
      ·
        refine ⟨32437722649072096085434627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43250296865429461447246169 32437722649072096085434627)
        ·
          refine ⟨48656583973608144128151941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32437722649072096085434627 48656583973608144128151941)
          ·
            refine ⟨9123109495051527024028489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48656583973608144128151941 9123109495051527024028489)
            ·
              refine ⟨6842332121288645268021367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9123109495051527024028489 6842332121288645268021367)
              ·
                refine ⟨10263498181932967902032051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842332121288645268021367 10263498181932967902032051)
                ·
                  refine ⟨15395247272899451853048077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10263498181932967902032051 15395247272899451853048077)
                  ·
                    refine ⟨5773217727337294444893029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15395247272899451853048077 5773217727337294444893029)
                    ·
                      refine ⟨1082478323875742708417443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5773217727337294444893029 1082478323875742708417443)
                      ·
                        rfl

theorem cell23_2108119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2108119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108119 prefixEnd_2108119 := by exact prefixLift 2108119
  have htrace : WordTrace (prefixWord ++ tailWord_2108119) baseStart_2108119 baseEnd_2108119 := by
    simpa [prefixWord, tailWord_2108119, baseEnd_2108119] using wordTrace_append hprefix tailTrace_2108119
  have hstable : (prefixWord ++ tailWord_2108119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108119).length < 2 ^ (prefixWord ++ tailWord_2108119).sum := by decide
  have hdescent : baseEnd_2108119 < baseStart_2108119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108148 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2108148 : Nat := 118140960795 + 2108148 * 2 ^ 59
def prefixEnd_2108148 : Nat := 4983230072969 + 3 ^ 40 * 2108148 * 2
def baseEnd_2108148 : Nat := 1082493214814723094954811

theorem tailTrace_2108148 : CollatzResearch.WordTrace tailWord_2108148 prefixEnd_2108148 1082493214814723094954811 := by
  unfold tailWord_2108148
  simp only [CollatzResearch.WordTrace]
  refine ⟨38445237183273656929510549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51260316244364875906014065 38445237183273656929510549)
  ·
    refine ⟨1802120492965952668570807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38445237183273656929510549 1802120492965952668570807)
    ·
      refine ⟨2703180739448929002856211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802120492965952668570807 2703180739448929002856211)
      ·
        refine ⟨4054771109173393504284317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703180739448929002856211 4054771109173393504284317)
        ·
          refine ⟨1520539165940022564106619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4054771109173393504284317 1520539165940022564106619)
          ·
            refine ⟨2280808748910033846159929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520539165940022564106619 2280808748910033846159929)
            ·
              refine ⟨1710606561682525384619947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280808748910033846159929 1710606561682525384619947)
              ·
                refine ⟨2565909842523788076929921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710606561682525384619947 2565909842523788076929921)
                ·
                  refine ⟨1924432381892841057697441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565909842523788076929921 1924432381892841057697441)
                  ·
                    refine ⟨1443324286419630793273081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924432381892841057697441 1443324286419630793273081)
                    ·
                      refine ⟨1082493214814723094954811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443324286419630793273081 1082493214814723094954811)
                      ·
                        rfl

theorem cell23_2108148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2108148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108148 prefixEnd_2108148 := by exact prefixLift 2108148
  have htrace : WordTrace (prefixWord ++ tailWord_2108148) baseStart_2108148 baseEnd_2108148 := by
    simpa [prefixWord, tailWord_2108148, baseEnd_2108148] using wordTrace_append hprefix tailTrace_2108148
  have hstable : (prefixWord ++ tailWord_2108148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108148).length < 2 ^ (prefixWord ++ tailWord_2108148).sum := by decide
  have hdescent : baseEnd_2108148 < baseStart_2108148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108169 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_2108169 : Nat := 118140960795 + 2108169 * 2 ^ 59
def prefixEnd_2108169 : Nat := 4983230072969 + 3 ^ 40 * 2108169 * 2
def baseEnd_2108169 : Nat := 1082503997908467512792213

theorem tailTrace_2108169 : CollatzResearch.WordTrace tailWord_2108169 prefixEnd_2108169 1082503997908467512792213 := by
  unfold tailWord_2108169
  simp only [CollatzResearch.WordTrace]
  refine ⟨76891240299471234445535561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51260826866314156297023707 76891240299471234445535561)
  ·
    refine ⟨57668430224603425834151671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76891240299471234445535561 57668430224603425834151671)
    ·
      refine ⟨86502645336905138751227507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57668430224603425834151671 86502645336905138751227507)
      ·
        refine ⟨129753968005357708126841261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86502645336905138751227507 129753968005357708126841261)
        ·
          refine ⟨48657738002009140547565473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129753968005357708126841261 48657738002009140547565473)
          ·
            refine ⟨36493303501506855410674105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48657738002009140547565473 36493303501506855410674105)
            ·
              refine ⟨27369977626130141558005579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36493303501506855410674105 27369977626130141558005579)
              ·
                refine ⟨41054966439195212337008369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27369977626130141558005579 41054966439195212337008369)
                ·
                  refine ⟨30791224829396409252756277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41054966439195212337008369 30791224829396409252756277)
                  ·
                    refine ⟨2886677327755913367445901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30791224829396409252756277 2886677327755913367445901)
                    ·
                      refine ⟨1082503997908467512792213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886677327755913367445901 1082503997908467512792213)
                      ·
                        rfl

theorem cell23_2108169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_2108169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108169 prefixEnd_2108169 := by exact prefixLift 2108169
  have htrace : WordTrace (prefixWord ++ tailWord_2108169) baseStart_2108169 baseEnd_2108169 := by
    simpa [prefixWord, tailWord_2108169, baseEnd_2108169] using wordTrace_append hprefix tailTrace_2108169
  have hstable : (prefixWord ++ tailWord_2108169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108169).length < 2 ^ (prefixWord ++ tailWord_2108169).sum := by decide
  have hdescent : baseEnd_2108169 < baseStart_2108169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108229 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_2108229 : Nat := 118140960795 + 2108229 * 2 ^ 59
def prefixEnd_2108229 : Nat := 4983230072969 + 3 ^ 40 * 2108229 * 2
def baseEnd_2108229 : Nat := 1082534806747737278041937

theorem tailTrace_2108229 : CollatzResearch.WordTrace tailWord_2108229 prefixEnd_2108229 1082534806747737278041937 := by
  unfold tailWord_2108229
  simp only [CollatzResearch.WordTrace]
  refine ⟨76893428679253864692719741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51262285786169243128479827 76893428679253864692719741)
  ·
    refine ⟨28835035754720199259769903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76893428679253864692719741 28835035754720199259769903)
    ·
      refine ⟨43252553632080298889654855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28835035754720199259769903 43252553632080298889654855)
      ·
        refine ⟨64878830448120448334482283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43252553632080298889654855 64878830448120448334482283)
        ·
          refine ⟨97318245672180672501723425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64878830448120448334482283 97318245672180672501723425)
          ·
            refine ⟨72988684254135504376292569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97318245672180672501723425 72988684254135504376292569)
            ·
              refine ⟨54741513190601628282219427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72988684254135504376292569 54741513190601628282219427)
              ·
                refine ⟨82112269785902442423329141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54741513190601628282219427 82112269785902442423329141)
                ·
                  refine ⟨7698025292428353977187107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82112269785902442423329141 7698025292428353977187107)
                  ·
                    refine ⟨11547037938642530965780661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7698025292428353977187107 11547037938642530965780661)
                    ·
                      refine ⟨1082534806747737278041937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11547037938642530965780661 1082534806747737278041937)
                      ·
                        rfl

theorem cell23_2108229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_2108229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108229 prefixEnd_2108229 := by exact prefixLift 2108229
  have htrace : WordTrace (prefixWord ++ tailWord_2108229) baseStart_2108229 baseEnd_2108229 := by
    simpa [prefixWord, tailWord_2108229, baseEnd_2108229] using wordTrace_append hprefix tailTrace_2108229
  have hstable : (prefixWord ++ tailWord_2108229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108229).length < 2 ^ (prefixWord ++ tailWord_2108229).sum := by decide
  have hdescent : baseEnd_2108229 < baseStart_2108229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108236 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_2108236 : Nat := 118140960795 + 2108236 * 2 ^ 59
def prefixEnd_2108236 : Nat := 4983230072969 + 3 ^ 40 * 2108236 * 2
def baseEnd_2108236 : Nat := 360846133704106250218135

theorem tailTrace_2108236 : CollatzResearch.WordTrace tailWord_2108236 prefixEnd_2108236 360846133704106250218135 := by
  unfold tailWord_2108236
  simp only [CollatzResearch.WordTrace]
  refine ⟨38446841995114252444112281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51262455993485669925483041 38446841995114252444112281)
  ·
    refine ⟨28835131496335689333084211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38446841995114252444112281 28835131496335689333084211)
    ·
      refine ⟨43252697244503533999626317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28835131496335689333084211 43252697244503533999626317)
      ·
        refine ⟨16219761466688825249859869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43252697244503533999626317 16219761466688825249859869)
        ·
          refine ⟨6082410550008309468697451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16219761466688825249859869 6082410550008309468697451)
          ·
            refine ⟨9123615825012464203046177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082410550008309468697451 9123615825012464203046177)
            ·
              refine ⟨6842711868759348152284633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9123615825012464203046177 6842711868759348152284633)
              ·
                refine ⟨5132033901569511114213475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6842711868759348152284633 5132033901569511114213475)
                ·
                  refine ⟨7698050852354266671320213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5132033901569511114213475 7698050852354266671320213)
                  ·
                    refine ⟨360846133704106250218135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7698050852354266671320213 360846133704106250218135)
                    ·
                      rfl

theorem cell23_2108236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_2108236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108236 prefixEnd_2108236 := by exact prefixLift 2108236
  have htrace : WordTrace (prefixWord ++ tailWord_2108236) baseStart_2108236 baseEnd_2108236 := by
    simpa [prefixWord, tailWord_2108236, baseEnd_2108236] using wordTrace_append hprefix tailTrace_2108236
  have hstable : (prefixWord ++ tailWord_2108236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108236).length < 2 ^ (prefixWord ++ tailWord_2108236).sum := by decide
  have hdescent : baseEnd_2108236 < baseStart_2108236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108249 : List Nat := [1, 2, 1, 2, 2, 5, 10]
def baseStart_2108249 : Nat := 118140960795 + 2108249 * 2 ^ 59
def prefixEnd_2108249 : Nat := 4983230072969 + 3 ^ 40 * 2108249 * 2
def baseEnd_2108249 : Nat := 13364754029146014812245

theorem tailTrace_2108249 : CollatzResearch.WordTrace tailWord_2108249 prefixEnd_2108249 13364754029146014812245 := by
  unfold tailWord_2108249
  simp only [CollatzResearch.WordTrace]
  refine ⟨76894158139181408108447801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51262772092787605405631867 76894158139181408108447801)
  ·
    refine ⟨57670618604386056081335851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76894158139181408108447801 57670618604386056081335851)
    ·
      refine ⟨86505927906579084122003777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57670618604386056081335851 86505927906579084122003777)
      ·
        refine ⟨64879445929934313091502833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86505927906579084122003777 64879445929934313091502833)
        ·
          refine ⟨48659584447450734818627125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64879445929934313091502833 48659584447450734818627125)
          ·
            refine ⟨4561836041948506389246293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48659584447450734818627125 4561836041948506389246293)
            ·
              refine ⟨13364754029146014812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4561836041948506389246293 13364754029146014812245)
              ·
                rfl

theorem cell23_2108249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 10].length) (baseStart_2108249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108249 prefixEnd_2108249 := by exact prefixLift 2108249
  have htrace : WordTrace (prefixWord ++ tailWord_2108249) baseStart_2108249 baseEnd_2108249 := by
    simpa [prefixWord, tailWord_2108249, baseEnd_2108249] using wordTrace_append hprefix tailTrace_2108249
  have hstable : (prefixWord ++ tailWord_2108249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108249).length < 2 ^ (prefixWord ++ tailWord_2108249).sum := by decide
  have hdescent : baseEnd_2108249 < baseStart_2108249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108260 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_2108260 : Nat := 118140960795 + 2108260 * 2 ^ 59
def prefixEnd_2108260 : Nat := 4983230072969 + 3 ^ 40 * 2108260 * 2
def baseEnd_2108260 : Nat := 1082550724648026656754295

theorem tailTrace_2108260 : CollatzResearch.WordTrace tailWord_2108260 prefixEnd_2108260 1082550724648026656754295 := by
  unfold tailWord_2108260
  simp only [CollatzResearch.WordTrace]
  refine ⟨38447279671070778493549117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51263039561427704658065489 38447279671070778493549117)
  ·
    refine ⟨14417729876651541935080919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38447279671070778493549117 14417729876651541935080919)
    ·
      refine ⟨21626594814977312902621379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14417729876651541935080919 21626594814977312902621379)
      ·
        refine ⟨32439892222465969353932069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21626594814977312902621379 32439892222465969353932069)
        ·
          refine ⟨6082479791712369253862263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32439892222465969353932069 6082479791712369253862263)
          ·
            refine ⟨9123719687568553880793395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6082479791712369253862263 9123719687568553880793395)
            ·
              refine ⟨13685579531352830821190093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123719687568553880793395 13685579531352830821190093)
              ·
                refine ⟨5132092324257311557946285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13685579531352830821190093 5132092324257311557946285)
                ·
                  refine ⟨1924534621596491834229857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5132092324257311557946285 1924534621596491834229857)
                  ·
                    refine ⟨1443400966197368875672393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924534621596491834229857 1443400966197368875672393)
                    ·
                      refine ⟨1082550724648026656754295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443400966197368875672393 1082550724648026656754295)
                      ·
                        rfl

theorem cell23_2108260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_2108260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108260 prefixEnd_2108260 := by exact prefixLift 2108260
  have htrace : WordTrace (prefixWord ++ tailWord_2108260) baseStart_2108260 baseEnd_2108260 := by
    simpa [prefixWord, tailWord_2108260, baseEnd_2108260] using wordTrace_append hprefix tailTrace_2108260
  have hstable : (prefixWord ++ tailWord_2108260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108260).length < 2 ^ (prefixWord ++ tailWord_2108260).sum := by decide
  have hdescent : baseEnd_2108260 < baseStart_2108260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108270 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2108270 : Nat := 118140960795 + 2108270 * 2 ^ 59
def prefixEnd_2108270 : Nat := 4983230072969 + 3 ^ 40 * 2108270 * 2
def baseEnd_2108270 : Nat := 360851953151523872543083

theorem tailTrace_2108270 : CollatzResearch.WordTrace tailWord_2108270 prefixEnd_2108270 360851953151523872543083 := by
  unfold tailWord_2108270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611865509013166086870283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51263282714736885796641509 9611865509013166086870283)
  ·
    refine ⟨14417798263519749130305425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9611865509013166086870283 14417798263519749130305425)
    ·
      refine ⟨10813348697639811847729069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14417798263519749130305425 10813348697639811847729069)
      ·
        refine ⟨4055005761614929442898401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10813348697639811847729069 4055005761614929442898401)
        ·
          refine ⟨3041254321211197082173801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4055005761614929442898401 3041254321211197082173801)
          ·
            refine ⟨2280940740908397811630351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041254321211197082173801 2280940740908397811630351)
            ·
              refine ⟨3421411111362596717445527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280940740908397811630351 3421411111362596717445527)
              ·
                refine ⟨5132116667043895076168291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421411111362596717445527 5132116667043895076168291)
                ·
                  refine ⟨7698175000565842614252437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5132116667043895076168291 7698175000565842614252437)
                  ·
                    refine ⟨360851953151523872543083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7698175000565842614252437 360851953151523872543083)
                    ·
                      rfl

theorem cell23_2108270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2108270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108270 prefixEnd_2108270 := by exact prefixLift 2108270
  have htrace : WordTrace (prefixWord ++ tailWord_2108270) baseStart_2108270 baseEnd_2108270 := by
    simpa [prefixWord, tailWord_2108270, baseEnd_2108270] using wordTrace_append hprefix tailTrace_2108270
  have hstable : (prefixWord ++ tailWord_2108270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108270).length < 2 ^ (prefixWord ++ tailWord_2108270).sum := by decide
  have hdescent : baseEnd_2108270 < baseStart_2108270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108273 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_2108273 : Nat := 118140960795 + 2108273 * 2 ^ 59
def prefixEnd_2108273 : Nat := 4983230072969 + 3 ^ 40 * 2108273 * 2
def baseEnd_2108273 : Nat := 1082557399896535105891735

theorem tailTrace_2108273 : CollatzResearch.WordTrace tailWord_2108273 prefixEnd_2108273 1082557399896535105891735 := by
  unfold tailWord_2108273
  simp only [CollatzResearch.WordTrace]
  refine ⟨76895033491094460207321473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51263355660729640138214315 76895033491094460207321473)
  ·
    refine ⟨57671275118320845155491105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76895033491094460207321473 57671275118320845155491105)
    ·
      refine ⟨43253456338740633866618329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57671275118320845155491105 43253456338740633866618329)
      ·
        refine ⟨32440092254055475399963747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43253456338740633866618329 32440092254055475399963747)
        ·
          refine ⟨48660138381083213099945621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32440092254055475399963747 48660138381083213099945621)
          ·
            refine ⟨2280943986613275614059951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48660138381083213099945621 2280943986613275614059951)
            ·
              refine ⟨3421415979919913421089927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280943986613275614059951 3421415979919913421089927)
              ·
                refine ⟨5132123969879870131634891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421415979919913421089927 5132123969879870131634891)
                ·
                  refine ⟨7698185954819805197452337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5132123969879870131634891 7698185954819805197452337)
                  ·
                    refine ⟨5773639466114853898089253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7698185954819805197452337 5773639466114853898089253)
                    ·
                      refine ⟨1082557399896535105891735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5773639466114853898089253 1082557399896535105891735)
                      ·
                        rfl

theorem cell23_2108273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_2108273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108273 prefixEnd_2108273 := by exact prefixLift 2108273
  have htrace : WordTrace (prefixWord ++ tailWord_2108273) baseStart_2108273 baseEnd_2108273 := by
    simpa [prefixWord, tailWord_2108273, baseEnd_2108273] using wordTrace_append hprefix tailTrace_2108273
  have hstable : (prefixWord ++ tailWord_2108273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108273).length < 2 ^ (prefixWord ++ tailWord_2108273).sum := by decide
  have hdescent : baseEnd_2108273 < baseStart_2108273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108279 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 7]
def baseStart_2108279 : Nat := 118140960795 + 2108279 * 2 ^ 59
def prefixEnd_2108279 : Nat := 4983230072969 + 3 ^ 40 * 2108279 * 2
def baseEnd_2108279 : Nat := 360853493593487360805569

theorem tailTrace_2108279 : CollatzResearch.WordTrace tailWord_2108279 prefixEnd_2108279 360853493593487360805569 := by
  unfold tailWord_2108279
  simp only [CollatzResearch.WordTrace]
  refine ⟨76895252329072723232039891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51263501552715148821359927 76895252329072723232039891)
  ·
    refine ⟨115342878493609084848059837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76895252329072723232039891 115342878493609084848059837)
    ·
      refine ⟨43253579435103406818022439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115342878493609084848059837 43253579435103406818022439)
      ·
        refine ⟨64880369152655110227033659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43253579435103406818022439 64880369152655110227033659)
        ·
          refine ⟨97320553728982665340550489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64880369152655110227033659 97320553728982665340550489)
          ·
            refine ⟨72990415296736999005412867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97320553728982665340550489 72990415296736999005412867)
            ·
              refine ⟨109485622945105498508119301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72990415296736999005412867 109485622945105498508119301)
              ·
                refine ⟨20528554302207280970272369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109485622945105498508119301 20528554302207280970272369)
                ·
                  refine ⟨15396415726655460727704277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20528554302207280970272369 15396415726655460727704277)
                  ·
                    refine ⟨360853493593487360805569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15396415726655460727704277 360853493593487360805569)
                    ·
                      rfl

theorem cell23_2108279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_2108279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108279 prefixEnd_2108279 := by exact prefixLift 2108279
  have htrace : WordTrace (prefixWord ++ tailWord_2108279) baseStart_2108279 baseEnd_2108279 := by
    simpa [prefixWord, tailWord_2108279, baseEnd_2108279] using wordTrace_append hprefix tailTrace_2108279
  have hstable : (prefixWord ++ tailWord_2108279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108279).length < 2 ^ (prefixWord ++ tailWord_2108279).sum := by decide
  have hdescent : baseEnd_2108279 < baseStart_2108279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108293 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_2108293 : Nat := 118140960795 + 2108293 * 2 ^ 59
def prefixEnd_2108293 : Nat := 4983230072969 + 3 ^ 40 * 2108293 * 2
def baseEnd_2108293 : Nat := 1082567669509625027641643

theorem tailTrace_2108293 : CollatzResearch.WordTrace tailWord_2108293 prefixEnd_2108293 1082567669509625027641643 := by
  unfold tailWord_2108293
  simp only [CollatzResearch.WordTrace]
  refine ⟨76895762951022003623049533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51263841967348002415366355 76895762951022003623049533)
  ·
    refine ⟨28835911106633251358643575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76895762951022003623049533 28835911106633251358643575)
    ·
      refine ⟨43253866659949877037965363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28835911106633251358643575 43253866659949877037965363)
      ·
        refine ⟨64880799989924815556948045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43253866659949877037965363 64880799989924815556948045)
        ·
          refine ⟨24330299996221805833855517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64880799989924815556948045 24330299996221805833855517)
          ·
            refine ⟨9123862498583177187695819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24330299996221805833855517 9123862498583177187695819)
            ·
              refine ⟨13685793747874765781543729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123862498583177187695819 13685793747874765781543729)
              ·
                refine ⟨10264345310906074336157797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13685793747874765781543729 10264345310906074336157797)
                ·
                  refine ⟨1924564745794888938029587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10264345310906074336157797 1924564745794888938029587)
                  ·
                    refine ⟨2886847118692333407044381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1924564745794888938029587 2886847118692333407044381)
                    ·
                      refine ⟨1082567669509625027641643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886847118692333407044381 1082567669509625027641643)
                      ·
                        rfl

theorem cell23_2108293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_2108293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108293 prefixEnd_2108293 := by exact prefixLift 2108293
  have htrace : WordTrace (prefixWord ++ tailWord_2108293) baseStart_2108293 baseEnd_2108293 := by
    simpa [prefixWord, tailWord_2108293, baseEnd_2108293] using wordTrace_append hprefix tailTrace_2108293
  have hstable : (prefixWord ++ tailWord_2108293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108293).length < 2 ^ (prefixWord ++ tailWord_2108293).sum := by decide
  have hdescent : baseEnd_2108293 < baseStart_2108293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108327 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2108327 : Nat := 118140960795 + 2108327 * 2 ^ 59
def prefixEnd_2108327 : Nat := 4983230072969 + 3 ^ 40 * 2108327 * 2
def baseEnd_2108327 : Nat := 1082585127851877894616487

theorem tailTrace_2108327 : CollatzResearch.WordTrace tailWord_2108327 prefixEnd_2108327 1082585127851877894616487 := by
  unfold tailWord_2108327
  simp only [CollatzResearch.WordTrace]
  refine ⟨76897003032898827429787235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51264668688599218286524823 76897003032898827429787235)
  ·
    refine ⟨115345504549348241144680853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76897003032898827429787235 115345504549348241144680853)
    ·
      refine ⟨5406820525750698803656915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115345504549348241144680853 5406820525750698803656915)
      ·
        refine ⟨8110230788626048205485373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406820525750698803656915 8110230788626048205485373)
        ·
          refine ⟨3041336545734768077057015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8110230788626048205485373 3041336545734768077057015)
          ·
            refine ⟨4562004818602152115585523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041336545734768077057015 4562004818602152115585523)
            ·
              refine ⟨6843007227903228173378285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562004818602152115585523 6843007227903228173378285)
              ·
                refine ⟨2566127710463710565016857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6843007227903228173378285 2566127710463710565016857)
                ·
                  refine ⟨1924595782847782923762643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566127710463710565016857 1924595782847782923762643)
                  ·
                    refine ⟨2886893674271674385643965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1924595782847782923762643 2886893674271674385643965)
                    ·
                      refine ⟨1082585127851877894616487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2886893674271674385643965 1082585127851877894616487)
                      ·
                        rfl

theorem cell23_2108327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2108327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108327 prefixEnd_2108327 := by exact prefixLift 2108327
  have htrace : WordTrace (prefixWord ++ tailWord_2108327) baseStart_2108327 baseEnd_2108327 := by
    simpa [prefixWord, tailWord_2108327, baseEnd_2108327] using wordTrace_append hprefix tailTrace_2108327
  have hstable : (prefixWord ++ tailWord_2108327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108327).length < 2 ^ (prefixWord ++ tailWord_2108327).sum := by decide
  have hdescent : baseEnd_2108327 < baseStart_2108327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108350 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_2108350 : Nat := 118140960795 + 2108350 * 2 ^ 59
def prefixEnd_2108350 : Nat := 4983230072969 + 3 ^ 40 * 2108350 * 2
def baseEnd_2108350 : Nat := 1082596937906931304628881

theorem tailTrace_2108350 : CollatzResearch.WordTrace tailWord_2108350 prefixEnd_2108350 1082596937906931304628881 := by
  unfold tailWord_2108350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612230238976937794734313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51265227941210334905249669 9612230238976937794734313)
  ·
    refine ⟨7209172679232703346050735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9612230238976937794734313 7209172679232703346050735)
    ·
      refine ⟨10813759018849055019076103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7209172679232703346050735 10813759018849055019076103)
      ·
        refine ⟨16220638528273582528614155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10813759018849055019076103 16220638528273582528614155)
        ·
          refine ⟨24330957792410373792921233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16220638528273582528614155 24330957792410373792921233)
          ·
            refine ⟨18248218344307780344690925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24330957792410373792921233 18248218344307780344690925)
            ·
              refine ⟨6843081879115417629259097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18248218344307780344690925 6843081879115417629259097)
              ·
                refine ⟨5132311409336563221944323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6843081879115417629259097 5132311409336563221944323)
                ·
                  refine ⟨7698467114004844832916485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5132311409336563221944323 7698467114004844832916485)
                  ·
                    refine ⟨1443462583875908406171841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7698467114004844832916485 1443462583875908406171841)
                    ·
                      refine ⟨1082596937906931304628881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443462583875908406171841 1082596937906931304628881)
                      ·
                        rfl

theorem cell23_2108350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_2108350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108350 prefixEnd_2108350 := by exact prefixLift 2108350
  have htrace : WordTrace (prefixWord ++ tailWord_2108350) baseStart_2108350 baseEnd_2108350 := by
    simpa [prefixWord, tailWord_2108350, baseEnd_2108350] using wordTrace_append hprefix tailTrace_2108350
  have hstable : (prefixWord ++ tailWord_2108350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108350).length < 2 ^ (prefixWord ++ tailWord_2108350).sum := by decide
  have hdescent : baseEnd_2108350 < baseStart_2108350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108367 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 2, 2, 2]
def baseStart_2108367 : Nat := 118140960795 + 2108367 * 2 ^ 59
def prefixEnd_2108367 : Nat := 4983230072969 + 3 ^ 40 * 2108367 * 2
def baseEnd_2108367 : Nat := 1082605667078057738116303

theorem tailTrace_2108367 : CollatzResearch.WordTrace tailWord_2108367 prefixEnd_2108367 1082605667078057738116303 := by
  unfold tailWord_2108367
  simp only [CollatzResearch.WordTrace]
  refine ⟨76898461952753914261243355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51265641301835942840828903 76898461952753914261243355)
  ·
    refine ⟨115347692929130871391865033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76898461952753914261243355 115347692929130871391865033)
    ·
      refine ⟨86510769696848153543898775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115347692929130871391865033 86510769696848153543898775)
      ·
        refine ⟨129766154545272230315848163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86510769696848153543898775 129766154545272230315848163)
        ·
          refine ⟨194649231817908345473772245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129766154545272230315848163 194649231817908345473772245)
          ·
            refine ⟨4562091370732226847041537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 194649231817908345473772245 4562091370732226847041537)
            ·
              refine ⟨3421568528049170135281153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562091370732226847041537 3421568528049170135281153)
              ·
                refine ⟨2566176396036877601460865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421568528049170135281153 2566176396036877601460865)
                ·
                  refine ⟨1924632297027658201095649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566176396036877601460865 1924632297027658201095649)
                  ·
                    refine ⟨1443474222770743650821737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924632297027658201095649 1443474222770743650821737)
                    ·
                      refine ⟨1082605667078057738116303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443474222770743650821737 1082605667078057738116303)
                      ·
                        rfl

theorem cell23_2108367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2, 2].length) (baseStart_2108367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108367 prefixEnd_2108367 := by exact prefixLift 2108367
  have htrace : WordTrace (prefixWord ++ tailWord_2108367) baseStart_2108367 baseEnd_2108367 := by
    simpa [prefixWord, tailWord_2108367, baseEnd_2108367] using wordTrace_append hprefix tailTrace_2108367
  have hstable : (prefixWord ++ tailWord_2108367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108367).length < 2 ^ (prefixWord ++ tailWord_2108367).sum := by decide
  have hdescent : baseEnd_2108367 < baseStart_2108367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108418 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2108418 : Nat := 118140960795 + 2108418 * 2 ^ 59
def prefixEnd_2108418 : Nat := 4983230072969 + 3 ^ 40 * 2108418 * 2
def baseEnd_2108418 : Nat := 1082631854591437038578569

theorem tailTrace_2108418 : CollatzResearch.WordTrace tailWord_2108418 prefixEnd_2108418 1082631854591437038578569 := by
  unfold tailWord_2108418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19225080518892287492837477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51266881383712766647566605 19225080518892287492837477)
  ·
    refine ⟨3604702597292303904907027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19225080518892287492837477 3604702597292303904907027)
    ·
      refine ⟨5407053895938455857360541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3604702597292303904907027 5407053895938455857360541)
      ·
        refine ⟨2027645210976920946510203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5407053895938455857360541 2027645210976920946510203)
        ·
          refine ⟨3041467816465381419765305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027645210976920946510203 3041467816465381419765305)
          ·
            refine ⟨2281100862349036064823979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041467816465381419765305 2281100862349036064823979)
            ·
              refine ⟨3421651293523554097235969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281100862349036064823979 3421651293523554097235969)
              ·
                refine ⟨2566238470142665572926977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421651293523554097235969 2566238470142665572926977)
                ·
                  refine ⟨1924678852606999179695233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566238470142665572926977 1924678852606999179695233)
                  ·
                    refine ⟨1443509139455249384771425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924678852606999179695233 1443509139455249384771425)
                    ·
                      refine ⟨1082631854591437038578569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443509139455249384771425 1082631854591437038578569)
                      ·
                        rfl

theorem cell23_2108418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2108418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108418 prefixEnd_2108418 := by exact prefixLift 2108418
  have htrace : WordTrace (prefixWord ++ tailWord_2108418) baseStart_2108418 baseEnd_2108418 := by
    simpa [prefixWord, tailWord_2108418, baseEnd_2108418] using wordTrace_append hprefix tailTrace_2108418
  have hstable : (prefixWord ++ tailWord_2108418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108418).length < 2 ^ (prefixWord ++ tailWord_2108418).sum := by decide
  have hdescent : baseEnd_2108418 < baseStart_2108418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108423 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2108423 : Nat := 118140960795 + 2108423 * 2 ^ 59
def prefixEnd_2108423 : Nat := 4983230072969 + 3 ^ 40 * 2108423 * 2
def baseEnd_2108423 : Nat := 1082634421994709519016045

theorem tailTrace_2108423 : CollatzResearch.WordTrace tailWord_2108423 prefixEnd_2108423 1082634421994709519016045 := by
  unfold tailWord_2108423
  simp only [CollatzResearch.WordTrace]
  refine ⟨76900504440551035825281923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51267002960367357216854615 76900504440551035825281923)
  ·
    refine ⟨115350756660826553737922885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76900504440551035825281923 115350756660826553737922885)
    ·
      refine ⟨21628266873904978825860541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115350756660826553737922885 21628266873904978825860541)
      ·
        refine ⟨8110600077714367059697703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21628266873904978825860541 8110600077714367059697703)
        ·
          refine ⟨12165900116571550589546555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8110600077714367059697703 12165900116571550589546555)
          ·
            refine ⟨18248850174857325884319833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12165900116571550589546555 18248850174857325884319833)
            ·
              refine ⟨13686637631142994413239875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18248850174857325884319833 13686637631142994413239875)
              ·
                refine ⟨20529956446714491619859813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13686637631142994413239875 20529956446714491619859813)
                ·
                  refine ⟨3849366833758967178723715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20529956446714491619859813 3849366833758967178723715)
                  ·
                    refine ⟨5774050250638450768085573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3849366833758967178723715 5774050250638450768085573)
                    ·
                      refine ⟨1082634421994709519016045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5774050250638450768085573 1082634421994709519016045)
                      ·
                        rfl

theorem cell23_2108423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2108423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108423 prefixEnd_2108423 := by exact prefixLift 2108423
  have htrace : WordTrace (prefixWord ++ tailWord_2108423) baseStart_2108423 baseEnd_2108423 := by
    simpa [prefixWord, tailWord_2108423, baseEnd_2108423] using wordTrace_append hprefix tailTrace_2108423
  have hstable : (prefixWord ++ tailWord_2108423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108423).length < 2 ^ (prefixWord ++ tailWord_2108423).sum := by decide
  have hdescent : baseEnd_2108423 < baseStart_2108423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108440 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2108440 : Nat := 118140960795 + 2108440 * 2 ^ 59
def prefixEnd_2108440 : Nat := 4983230072969 + 3 ^ 40 * 2108440 * 2
def baseEnd_2108440 : Nat := 1082643151165835952503467

theorem tailTrace_2108440 : CollatzResearch.WordTrace tailWord_2108440 prefixEnd_2108440 1082643151165835952503467 := by
  unfold tailWord_2108440
  simp only [CollatzResearch.WordTrace]
  refine ⟨38450562240744723864325387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51267416320992965152433849 38450562240744723864325387)
  ·
    refine ⟨57675843361117085796488081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38450562240744723864325387 57675843361117085796488081)
    ·
      refine ⟨43256882520837814347366061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57675843361117085796488081 43256882520837814347366061)
      ·
        refine ⟨16221330945314180380262273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43256882520837814347366061 16221330945314180380262273)
        ·
          refine ⟨12165998208985635285196705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16221330945314180380262273 12165998208985635285196705)
          ·
            refine ⟨9124498656739226463897529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12165998208985635285196705 9124498656739226463897529)
            ·
              refine ⟨6843373992554419847923147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9124498656739226463897529 6843373992554419847923147)
              ·
                refine ⟨10265060988831629771884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6843373992554419847923147 10265060988831629771884721)
                ·
                  refine ⟨7698795741623722328913541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10265060988831629771884721 7698795741623722328913541)
                  ·
                    refine ⟨1443524201554447936671289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7698795741623722328913541 1443524201554447936671289)
                    ·
                      refine ⟨1082643151165835952503467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443524201554447936671289 1082643151165835952503467)
                      ·
                        rfl

theorem cell23_2108440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2108440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108440 prefixEnd_2108440 := by exact prefixLift 2108440
  have htrace : WordTrace (prefixWord ++ tailWord_2108440) baseStart_2108440 baseEnd_2108440 := by
    simpa [prefixWord, tailWord_2108440, baseEnd_2108440] using wordTrace_append hprefix tailTrace_2108440
  have hstable : (prefixWord ++ tailWord_2108440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108440).length < 2 ^ (prefixWord ++ tailWord_2108440).sum := by decide
  have hdescent : baseEnd_2108440 < baseStart_2108440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108450 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2108450 : Nat := 118140960795 + 2108450 * 2 ^ 59
def prefixEnd_2108450 : Nat := 4983230072969 + 3 ^ 40 * 2108450 * 2
def baseEnd_2108450 : Nat := 360882761990793637792807

theorem tailTrace_2108450 : CollatzResearch.WordTrace tailWord_2108450 prefixEnd_2108450 360882761990793637792807 := by
  unfold tailWord_2108450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19225372302863304859128701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51267659474302146291009869 19225372302863304859128701)
  ·
    refine ⟨7209514613573739322173263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19225372302863304859128701 7209514613573739322173263)
    ·
      refine ⟨10814271920360608983259895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7209514613573739322173263 10814271920360608983259895)
      ·
        refine ⟨16221407880540913474889843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10814271920360608983259895 16221407880540913474889843)
        ·
          refine ⟨24332111820811370212334765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16221407880540913474889843 24332111820811370212334765)
          ·
            refine ⟨9124541932804263829625537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24332111820811370212334765 9124541932804263829625537)
            ·
              refine ⟨6843406449603197872219153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9124541932804263829625537 6843406449603197872219153)
              ·
                refine ⟨5132554837202398404164365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6843406449603197872219153 5132554837202398404164365)
                ·
                  refine ⟨1924708063950899401561637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5132554837202398404164365 1924708063950899401561637)
                  ·
                    refine ⟨360882761990793637792807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1924708063950899401561637 360882761990793637792807)
                    ·
                      rfl

theorem cell23_2108450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2108450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108450 prefixEnd_2108450 := by exact prefixLift 2108450
  have htrace : WordTrace (prefixWord ++ tailWord_2108450) baseStart_2108450 baseEnd_2108450 := by
    simpa [prefixWord, tailWord_2108450, baseEnd_2108450] using wordTrace_append hprefix tailTrace_2108450
  have hstable : (prefixWord ++ tailWord_2108450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108450).length < 2 ^ (prefixWord ++ tailWord_2108450).sum := by decide
  have hdescent : baseEnd_2108450 < baseStart_2108450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108500 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_2108500 : Nat := 118140960795 + 2108500 * 2 ^ 59
def prefixEnd_2108500 : Nat := 4983230072969 + 3 ^ 40 * 2108500 * 2
def baseEnd_2108500 : Nat := 1082673960005105717753191

theorem tailTrace_2108500 : CollatzResearch.WordTrace tailWord_2108500 prefixEnd_2108500 1082673960005105717753191 := by
  unfold tailWord_2108500
  simp only [CollatzResearch.WordTrace]
  refine ⟨38451656430636038987917477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51268875240848051983889969 38451656430636038987917477)
  ·
    refine ⟨7209685580744257310234527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38451656430636038987917477 7209685580744257310234527)
    ·
      refine ⟨10814528371116385965351791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7209685580744257310234527 10814528371116385965351791)
      ·
        refine ⟨16221792556674578948027687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10814528371116385965351791 16221792556674578948027687)
        ·
          refine ⟨24332688835011868422041531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16221792556674578948027687 24332688835011868422041531)
          ·
            refine ⟨36499033252517802633062297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24332688835011868422041531 36499033252517802633062297)
            ·
              refine ⟨27374274939388351974796723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36499033252517802633062297 27374274939388351974796723)
              ·
                refine ⟨41061412409082527962195085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27374274939388351974796723 41061412409082527962195085)
                ·
                  refine ⟨15398029653405947985823157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41061412409082527962195085 15398029653405947985823157)
                  ·
                    refine ⟨1443565280006807623670921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15398029653405947985823157 1443565280006807623670921)
                    ·
                      refine ⟨1082673960005105717753191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443565280006807623670921 1082673960005105717753191)
                      ·
                        rfl

theorem cell23_2108500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_2108500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108500 prefixEnd_2108500 := by exact prefixLift 2108500
  have htrace : WordTrace (prefixWord ++ tailWord_2108500) baseStart_2108500 baseEnd_2108500 := by
    simpa [prefixWord, tailWord_2108500, baseEnd_2108500] using wordTrace_append hprefix tailTrace_2108500
  have hstable : (prefixWord ++ tailWord_2108500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108500).length < 2 ^ (prefixWord ++ tailWord_2108500).sum := by decide
  have hdescent : baseEnd_2108500 < baseStart_2108500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108517 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_2108517 : Nat := 118140960795 + 2108517 * 2 ^ 59
def prefixEnd_2108517 : Nat := 4983230072969 + 3 ^ 40 * 2108517 * 2
def baseEnd_2108517 : Nat := 1082682689176232151240613

theorem tailTrace_2108517 : CollatzResearch.WordTrace tailWord_2108517 prefixEnd_2108517 1082682689176232151240613 := by
  unfold tailWord_2108517
  simp only [CollatzResearch.WordTrace]
  refine ⟨76903932902210489879203805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51269288601473659919469203 76903932902210489879203805)
  ·
    refine ⟨28838974838328933704701427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76903932902210489879203805 28838974838328933704701427)
    ·
      refine ⟨43258462257493400557052141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28838974838328933704701427 43258462257493400557052141)
      ·
        refine ⟨16221923346560025208894553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43258462257493400557052141 16221923346560025208894553)
        ·
          refine ⟨12166442509920018906670915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16221923346560025208894553 12166442509920018906670915)
          ·
            refine ⟨18249663764880028360006373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12166442509920018906670915 18249663764880028360006373)
            ·
              refine ⟨3421811955915005317501195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18249663764880028360006373 3421811955915005317501195)
              ·
                refine ⟨5132717933872507976251793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421811955915005317501195 5132717933872507976251793)
                ·
                  refine ⟨3849538450404380982188845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5132717933872507976251793 3849538450404380982188845)
                  ·
                    refine ⟨1443576918901642868320817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3849538450404380982188845 1443576918901642868320817)
                    ·
                      refine ⟨1082682689176232151240613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443576918901642868320817 1082682689176232151240613)
                      ·
                        rfl

theorem cell23_2108517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_2108517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108517 prefixEnd_2108517 := by exact prefixLift 2108517
  have htrace : WordTrace (prefixWord ++ tailWord_2108517) baseStart_2108517 baseEnd_2108517 := by
    simpa [prefixWord, tailWord_2108517, baseEnd_2108517] using wordTrace_append hprefix tailTrace_2108517
  have hstable : (prefixWord ++ tailWord_2108517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108517).length < 2 ^ (prefixWord ++ tailWord_2108517).sum := by decide
  have hdescent : baseEnd_2108517 < baseStart_2108517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108547 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 3, 2, 2]
def baseStart_2108547 : Nat := 118140960795 + 2108547 * 2 ^ 59
def prefixEnd_2108547 : Nat := 4983230072969 + 3 ^ 40 * 2108547 * 2
def baseEnd_2108547 : Nat := 1082698093595867033865475

theorem tailTrace_2108547 : CollatzResearch.WordTrace tailWord_2108547 prefixEnd_2108547 1082698093595867033865475 := by
  unfold tailWord_2108547
  simp only [CollatzResearch.WordTrace]
  refine ⟨76905027092101805002795895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51270018061401203335197263 76905027092101805002795895)
  ·
    refine ⟨115357540638152707504193843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76905027092101805002795895 115357540638152707504193843)
    ·
      refine ⟨173036310957229061256290765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115357540638152707504193843 173036310957229061256290765)
      ·
        refine ⟨64888616608960897971109037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173036310957229061256290765 64888616608960897971109037)
        ·
          refine ⟨24333231228360336739165889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64888616608960897971109037 24333231228360336739165889)
          ·
            refine ⟨18249923421270252554374417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24333231228360336739165889 18249923421270252554374417)
            ·
              refine ⟨13687442565952689415780813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18249923421270252554374417 13687442565952689415780813)
              ·
                refine ⟨5132790962232258530917805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13687442565952689415780813 5132790962232258530917805)
                ·
                  refine ⟨1924796610837096949094177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5132790962232258530917805 1924796610837096949094177)
                  ·
                    refine ⟨1443597458127822711820633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924796610837096949094177 1443597458127822711820633)
                    ·
                      refine ⟨1082698093595867033865475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443597458127822711820633 1082698093595867033865475)
                      ·
                        rfl

theorem cell23_2108547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_2108547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108547 prefixEnd_2108547 := by exact prefixLift 2108547
  have htrace : WordTrace (prefixWord ++ tailWord_2108547) baseStart_2108547 baseEnd_2108547 := by
    simpa [prefixWord, tailWord_2108547, baseEnd_2108547] using wordTrace_append hprefix tailTrace_2108547
  have hstable : (prefixWord ++ tailWord_2108547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108547).length < 2 ^ (prefixWord ++ tailWord_2108547).sum := by decide
  have hdescent : baseEnd_2108547 < baseStart_2108547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108553 : List Nat := [1, 2, 1, 1, 4, 3, 3, 8]
def baseStart_2108553 : Nat := 118140960795 + 2108553 * 2 ^ 59
def prefixEnd_2108553 : Nat := 4983230072969 + 3 ^ 40 * 2108553 * 2
def baseEnd_2108553 : Nat := 40100043499251630014461

theorem tailTrace_2108553 : CollatzResearch.WordTrace tailWord_2108553 prefixEnd_2108553 40100043499251630014461 := by
  unfold tailWord_2108553
  simp only [CollatzResearch.WordTrace]
  refine ⟨76905245930080068027514313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51270163953386712018342875 76905245930080068027514313)
  ·
    refine ⟨57678934447560051020635735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76905245930080068027514313 57678934447560051020635735)
    ·
      refine ⟨86518401671340076530953603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57678934447560051020635735 86518401671340076530953603)
      ·
        refine ⟨129777602507010114796430405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86518401671340076530953603 129777602507010114796430405)
        ·
          refine ⟨24333300470064396524330701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129777602507010114796430405 24333300470064396524330701)
          ·
            refine ⟨9124987676274148696624013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24333300470064396524330701 9124987676274148696624013)
            ·
              refine ⟨3421870378602805761234005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9124987676274148696624013 3421870378602805761234005)
              ·
                refine ⟨40100043499251630014461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3421870378602805761234005 40100043499251630014461)
                ·
                  rfl

theorem cell23_2108553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 8].length) (baseStart_2108553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108553 prefixEnd_2108553 := by exact prefixLift 2108553
  have htrace : WordTrace (prefixWord ++ tailWord_2108553) baseStart_2108553 baseEnd_2108553 := by
    simpa [prefixWord, tailWord_2108553, baseEnd_2108553] using wordTrace_append hprefix tailTrace_2108553
  have hstable : (prefixWord ++ tailWord_2108553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108553).length < 2 ^ (prefixWord ++ tailWord_2108553).sum := by decide
  have hdescent : baseEnd_2108553 < baseStart_2108553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108581 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 1, 2, 2]
def baseStart_2108581 : Nat := 118140960795 + 2108581 * 2 ^ 59
def prefixEnd_2108581 : Nat := 4983230072969 + 3 ^ 40 * 2108581 * 2
def baseEnd_2108581 : Nat := 1082715551938119900840319

theorem tailTrace_2108581 : CollatzResearch.WordTrace tailWord_2108581 prefixEnd_2108581 1082715551938119900840319 := by
  unfold tailWord_2108581
  simp only [CollatzResearch.WordTrace]
  refine ⟨76906267173978628809533597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51270844782652419206355731 76906267173978628809533597)
  ·
    refine ⟨28839850190241985803575099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76906267173978628809533597 28839850190241985803575099)
    ·
      refine ⟨43259775285362978705362649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28839850190241985803575099 43259775285362978705362649)
      ·
        refine ⟨32444831464022234029021987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43259775285362978705362649 32444831464022234029021987)
        ·
          refine ⟨48667247196033351043532981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32444831464022234029021987 48667247196033351043532981)
          ·
            refine ⟨4562554424628126660331217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48667247196033351043532981 4562554424628126660331217)
            ·
              refine ⟨3421915818471094995248413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562554424628126660331217 3421915818471094995248413)
              ·
                refine ⟨1283218431926660623218155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3421915818471094995248413 1283218431926660623218155)
                ·
                  refine ⟨1924827647889990934827233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283218431926660623218155 1924827647889990934827233)
                  ·
                    refine ⟨1443620735917493201120425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924827647889990934827233 1443620735917493201120425)
                    ·
                      refine ⟨1082715551938119900840319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443620735917493201120425 1082715551938119900840319)
                      ·
                        rfl

theorem cell23_2108581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_2108581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108581 prefixEnd_2108581 := by exact prefixLift 2108581
  have htrace : WordTrace (prefixWord ++ tailWord_2108581) baseStart_2108581 baseEnd_2108581 := by
    simpa [prefixWord, tailWord_2108581, baseEnd_2108581] using wordTrace_append hprefix tailTrace_2108581
  have hstable : (prefixWord ++ tailWord_2108581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108581).length < 2 ^ (prefixWord ++ tailWord_2108581).sum := by decide
  have hdescent : baseEnd_2108581 < baseStart_2108581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108603 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_2108603 : Nat := 118140960795 + 2108603 * 2 ^ 59
def prefixEnd_2108603 : Nat := 4983230072969 + 3 ^ 40 * 2108603 * 2
def baseEnd_2108603 : Nat := 1082726848512518814765217

theorem tailTrace_2108603 : CollatzResearch.WordTrace tailWord_2108603 prefixEnd_2108603 1082726848512518814765217 := by
  unfold tailWord_2108603
  simp only [CollatzResearch.WordTrace]
  refine ⟨76907069579898926566834463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51271379719932617711222975 76907069579898926566834463)
  ·
    refine ⟨115360604369848389850251695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76907069579898926566834463 115360604369848389850251695)
    ·
      refine ⟨173040906554772584775377543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115360604369848389850251695 173040906554772584775377543)
      ·
        refine ⟨259561359832158877163066315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173040906554772584775377543 259561359832158877163066315)
        ·
          refine ⟨389342039748238315744599473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259561359832158877163066315 389342039748238315744599473)
          ·
            refine ⟨292006529811178736808449605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389342039748238315744599473 292006529811178736808449605)
            ·
              refine ⟨54751224339596013151584301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 292006529811178736808449605 54751224339596013151584301)
              ·
                refine ⟨20531709127348504931844113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54751224339596013151584301 20531709127348504931844113)
                ·
                  refine ⟨15398781845511378698883085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20531709127348504931844113 15398781845511378698883085)
                  ·
                    refine ⟨5774543192066767012081157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15398781845511378698883085 5774543192066767012081157)
                    ·
                      refine ⟨1082726848512518814765217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5774543192066767012081157 1082726848512518814765217)
                      ·
                        rfl

theorem cell23_2108603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_2108603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108603 prefixEnd_2108603 := by exact prefixLift 2108603
  have htrace : WordTrace (prefixWord ++ tailWord_2108603) baseStart_2108603 baseEnd_2108603 := by
    simpa [prefixWord, tailWord_2108603, baseEnd_2108603] using wordTrace_append hprefix tailTrace_2108603
  have hstable : (prefixWord ++ tailWord_2108603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108603).length < 2 ^ (prefixWord ++ tailWord_2108603).sum := by decide
  have hdescent : baseEnd_2108603 < baseStart_2108603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108621 : List Nat := [1, 6, 2, 2, 1, 2, 2, 7]
def baseStart_2108621 : Nat := 118140960795 + 2108621 * 2 ^ 59
def prefixEnd_2108621 : Nat := 4983230072969 + 3 ^ 40 * 2108621 * 2
def baseEnd_2108621 : Nat := 40101336709788879420005

theorem tailTrace_2108621 : CollatzResearch.WordTrace tailWord_2108621 prefixEnd_2108621 40101336709788879420005 := by
  unfold tailWord_2108621
  simp only [CollatzResearch.WordTrace]
  refine ⟨76907726093833715640989717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51271817395889143760659811 76907726093833715640989717)
  ·
    refine ⟨3605049660648455420671393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76907726093833715640989717 3605049660648455420671393)
    ·
      refine ⟨2703787245486341565503545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3605049660648455420671393 2703787245486341565503545)
      ·
        refine ⟨2027840434114756174127659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2703787245486341565503545 2027840434114756174127659)
        ·
          refine ⟨3041760651172134261191489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027840434114756174127659 3041760651172134261191489)
          ·
            refine ⟨2281320488379100695893617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041760651172134261191489 2281320488379100695893617)
            ·
              refine ⟨1710990366284325521920213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281320488379100695893617 1710990366284325521920213)
              ·
                refine ⟨40101336709788879420005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1710990366284325521920213 40101336709788879420005)
                ·
                  rfl

theorem cell23_2108621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 7].length) (baseStart_2108621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108621 prefixEnd_2108621 := by exact prefixLift 2108621
  have htrace : WordTrace (prefixWord ++ tailWord_2108621) baseStart_2108621 baseEnd_2108621 := by
    simpa [prefixWord, tailWord_2108621, baseEnd_2108621] using wordTrace_append hprefix tailTrace_2108621
  have hstable : (prefixWord ++ tailWord_2108621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108621).length < 2 ^ (prefixWord ++ tailWord_2108621).sum := by decide
  have hdescent : baseEnd_2108621 < baseStart_2108621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108640 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2108640 : Nat := 118140960795 + 2108640 * 2 ^ 59
def prefixEnd_2108640 : Nat := 4983230072969 + 3 ^ 40 * 2108640 * 2
def baseEnd_2108640 : Nat := 1082745847296735170002547

theorem tailTrace_2108640 : CollatzResearch.WordTrace tailWord_2108640 prefixEnd_2108640 1082745847296735170002547 := by
  unfold tailWord_2108640
  simp only [CollatzResearch.WordTrace]
  refine ⟨38454209540382440942965687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51272279387176587923954249 38454209540382440942965687)
  ·
    refine ⟨57681314310573661414448531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38454209540382440942965687 57681314310573661414448531)
    ·
      refine ⟨86521971465860492121672797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57681314310573661414448531 86521971465860492121672797)
      ·
        refine ⟨32445739299697684545627299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86521971465860492121672797 32445739299697684545627299)
        ·
          refine ⟨48668608949546526818440949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32445739299697684545627299 48668608949546526818440949)
          ·
            refine ⟨4562682089019986889228839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48668608949546526818440949 4562682089019986889228839)
            ·
              refine ⟨6844023133529980333843259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562682089019986889228839 6844023133529980333843259)
              ·
                refine ⟨10266034700294970500764889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844023133529980333843259 10266034700294970500764889)
                ·
                  refine ⟨7699526025221227875573667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10266034700294970500764889 7699526025221227875573667)
                  ·
                    refine ⟨11549289037831841813360501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7699526025221227875573667 11549289037831841813360501)
                    ·
                      refine ⟨1082745847296735170002547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11549289037831841813360501 1082745847296735170002547)
                      ·
                        rfl

theorem cell23_2108640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2108640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108640 prefixEnd_2108640 := by exact prefixLift 2108640
  have htrace : WordTrace (prefixWord ++ tailWord_2108640) baseStart_2108640 baseEnd_2108640 := by
    simpa [prefixWord, tailWord_2108640, baseEnd_2108640] using wordTrace_append hprefix tailTrace_2108640
  have hstable : (prefixWord ++ tailWord_2108640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108640).length < 2 ^ (prefixWord ++ tailWord_2108640).sum := by decide
  have hdescent : baseEnd_2108640 < baseStart_2108640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108654 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_2108654 : Nat := 118140960795 + 2108654 * 2 ^ 59
def prefixEnd_2108654 : Nat := 4983230072969 + 3 ^ 40 * 2108654 * 2
def baseEnd_2108654 : Nat := 1082753036025898115227483

theorem tailTrace_2108654 : CollatzResearch.WordTrace tailWord_2108654 prefixEnd_2108654 1082753036025898115227483 := by
  unfold tailWord_2108654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613616212839270284617627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51272619801809441517960677 9613616212839270284617627)
  ·
    refine ⟨14420424319258905426926441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9613616212839270284617627 14420424319258905426926441)
    ·
      refine ⟨10815318239444179070194831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14420424319258905426926441 10815318239444179070194831)
      ·
        refine ⟨16222977359166268605292247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10815318239444179070194831 16222977359166268605292247)
        ·
          refine ⟨24334466038749402907938371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16222977359166268605292247 24334466038749402907938371)
          ·
            refine ⟨36501699058124104361907557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24334466038749402907938371 36501699058124104361907557)
            ·
              refine ⟨6844068573398269567857667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36501699058124104361907557 6844068573398269567857667)
              ·
                refine ⟨10266102860097404351786501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844068573398269567857667 10266102860097404351786501)
                ·
                  refine ⟨1924894286268263315959969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10266102860097404351786501 1924894286268263315959969)
                  ·
                    refine ⟨1443670714701197486969977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924894286268263315959969 1443670714701197486969977)
                    ·
                      refine ⟨1082753036025898115227483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443670714701197486969977 1082753036025898115227483)
                      ·
                        rfl

theorem cell23_2108654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_2108654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108654 prefixEnd_2108654 := by exact prefixLift 2108654
  have htrace : WordTrace (prefixWord ++ tailWord_2108654) baseStart_2108654 baseEnd_2108654 := by
    simpa [prefixWord, tailWord_2108654, baseEnd_2108654] using wordTrace_append hprefix tailTrace_2108654
  have hstable : (prefixWord ++ tailWord_2108654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108654).length < 2 ^ (prefixWord ++ tailWord_2108654).sum := by decide
  have hdescent : baseEnd_2108654 < baseStart_2108654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108671 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 2, 2, 2]
def baseStart_2108671 : Nat := 118140960795 + 2108671 * 2 ^ 59
def prefixEnd_2108671 : Nat := 4983230072969 + 3 ^ 40 * 2108671 * 2
def baseEnd_2108671 : Nat := 1082761765197024548714905

theorem tailTrace_2108671 : CollatzResearch.WordTrace tailWord_2108671 prefixEnd_2108671 1082761765197024548714905 := by
  unfold tailWord_2108671
  simp only [CollatzResearch.WordTrace]
  refine ⟨76909549743652574180309867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51273033162435049453539911 76909549743652574180309867)
  ·
    refine ⟨115364324615478861270464801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76909549743652574180309867 115364324615478861270464801)
    ·
      refine ⟨86523243461609145952848601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115364324615478861270464801 86523243461609145952848601)
      ·
        refine ⟨64892432596206859464636451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86523243461609145952848601 64892432596206859464636451)
        ·
          refine ⟨97338648894310289196954677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64892432596206859464636451 97338648894310289196954677)
          ·
            refine ⟨9125498333841589612214501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97338648894310289196954677 9125498333841589612214501)
            ·
              refine ⟨1711030937595298052290219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9125498333841589612214501 1711030937595298052290219)
              ·
                refine ⟨2566546406392947078435329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711030937595298052290219 2566546406392947078435329)
                ·
                  refine ⟨1924909804794710308826497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566546406392947078435329 1924909804794710308826497)
                  ·
                    refine ⟨1443682353596032731619873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1924909804794710308826497 1443682353596032731619873)
                    ·
                      refine ⟨1082761765197024548714905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443682353596032731619873 1082761765197024548714905)
                      ·
                        rfl

theorem cell23_2108671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_2108671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108671 prefixEnd_2108671 := by exact prefixLift 2108671
  have htrace : WordTrace (prefixWord ++ tailWord_2108671) baseStart_2108671 baseEnd_2108671 := by
    simpa [prefixWord, tailWord_2108671, baseEnd_2108671] using wordTrace_append hprefix tailTrace_2108671
  have hstable : (prefixWord ++ tailWord_2108671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108671).length < 2 ^ (prefixWord ++ tailWord_2108671).sum := by decide
  have hdescent : baseEnd_2108671 < baseStart_2108671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108700 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2108700 : Nat := 118140960795 + 2108700 * 2 ^ 59
def prefixEnd_2108700 : Nat := 4983230072969 + 3 ^ 40 * 2108700 * 2
def baseEnd_2108700 : Nat := 1082776656136004935252271

theorem tailTrace_2108700 : CollatzResearch.WordTrace tailWord_2108700 prefixEnd_2108700 1082776656136004935252271 := by
  unfold tailWord_2108700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38455303730273756066557777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51273738307031674755410369 38455303730273756066557777)
  ·
    refine ⟨28841477797705317049918333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38455303730273756066557777 28841477797705317049918333)
    ·
      refine ⟨10815554174139493893719375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28841477797705317049918333 10815554174139493893719375)
      ·
        refine ⟨16223331261209240840579063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10815554174139493893719375 16223331261209240840579063)
        ·
          refine ⟨24334996891813861260868595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16223331261209240840579063 24334996891813861260868595)
          ·
            refine ⟨36502495337720791891302893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24334996891813861260868595 36502495337720791891302893)
            ·
              refine ⟨13688435751645296959238585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36502495337720791891302893 13688435751645296959238585)
              ·
                refine ⟨10266326813733972719428939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13688435751645296959238585 10266326813733972719428939)
                ·
                  refine ⟨15399490220600959079143409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10266326813733972719428939 15399490220600959079143409)
                  ·
                    refine ⟨11549617665450719309357557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15399490220600959079143409 11549617665450719309357557)
                    ·
                      refine ⟨1082776656136004935252271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11549617665450719309357557 1082776656136004935252271)
                      ·
                        rfl

theorem cell23_2108700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2108700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108700 prefixEnd_2108700 := by exact prefixLift 2108700
  have htrace : WordTrace (prefixWord ++ tailWord_2108700) baseStart_2108700 baseEnd_2108700 := by
    simpa [prefixWord, tailWord_2108700, baseEnd_2108700] using wordTrace_append hprefix tailTrace_2108700
  have hstable : (prefixWord ++ tailWord_2108700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108700).length < 2 ^ (prefixWord ++ tailWord_2108700).sum := by decide
  have hdescent : baseEnd_2108700 < baseStart_2108700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108714 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2108714 : Nat := 118140960795 + 2108714 * 2 ^ 59
def prefixEnd_2108714 : Nat := 4983230072969 + 3 ^ 40 * 2108714 * 2
def baseEnd_2108714 : Nat := 1082783844865167880477207

theorem tailTrace_2108714 : CollatzResearch.WordTrace tailWord_2108714 prefixEnd_2108714 1082783844865167880477207 := by
  unfold tailWord_2108714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227779520624198131031299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51274078721664528349416797 19227779520624198131031299)
  ·
    refine ⟨28841669280936297196546949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227779520624198131031299 28841669280936297196546949)
    ·
      refine ⟨5407812990175555724352553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28841669280936297196546949 5407812990175555724352553)
      ·
        refine ⟨4055859742631666793264415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5407812990175555724352553 4055859742631666793264415)
        ·
          refine ⟨6083789613947500189896623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055859742631666793264415 6083789613947500189896623)
          ·
            refine ⟨9125684420921250284844935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083789613947500189896623 9125684420921250284844935)
            ·
              refine ⟨13688526631381875427267403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9125684420921250284844935 13688526631381875427267403)
              ·
                refine ⟨20532789947072813140901105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13688526631381875427267403 20532789947072813140901105)
                ·
                  refine ⟨15399592460304609855675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20532789947072813140901105 15399592460304609855675829)
                  ·
                    refine ⟨1443711793153557173969609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15399592460304609855675829 1443711793153557173969609)
                    ·
                      refine ⟨1082783844865167880477207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443711793153557173969609 1082783844865167880477207)
                      ·
                        rfl

theorem cell23_2108714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2108714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108714 prefixEnd_2108714 := by exact prefixLift 2108714
  have htrace : WordTrace (prefixWord ++ tailWord_2108714) baseStart_2108714 baseEnd_2108714 := by
    simpa [prefixWord, tailWord_2108714, baseEnd_2108714] using wordTrace_append hprefix tailTrace_2108714
  have hstable : (prefixWord ++ tailWord_2108714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108714).length < 2 ^ (prefixWord ++ tailWord_2108714).sum := by decide
  have hdescent : baseEnd_2108714 < baseStart_2108714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108750 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_2108750 : Nat := 118140960795 + 2108750 * 2 ^ 59
def prefixEnd_2108750 : Nat := 4983230072969 + 3 ^ 40 * 2108750 * 2
def baseEnd_2108750 : Nat := 120311370018747748847449

theorem tailTrace_2108750 : CollatzResearch.WordTrace tailWord_2108750 prefixEnd_2108750 120311370018747748847449 := by
  unfold tailWord_2108750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614053888795796334054463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51274954073577580448290469 9614053888795796334054463)
  ·
    refine ⟨14421080833193694501081695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9614053888795796334054463 14421080833193694501081695)
    ·
      refine ⟨21631621249790541751622543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14421080833193694501081695 21631621249790541751622543)
      ·
        refine ⟨32447431874685812627433815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21631621249790541751622543 32447431874685812627433815)
        ·
          refine ⟨48671147812028718941150723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32447431874685812627433815 48671147812028718941150723)
          ·
            refine ⟨73006721718043078411726085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48671147812028718941150723 73006721718043078411726085)
            ·
              refine ⟨13688760322133077202198641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73006721718043078411726085 13688760322133077202198641)
              ·
                refine ⟨10266570241599807901648981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13688760322133077202198641 10266570241599807901648981)
                ·
                  refine ⟨120311370018747748847449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10266570241599807901648981 120311370018747748847449)
                  ·
                    rfl

theorem cell23_2108750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_2108750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108750 prefixEnd_2108750 := by exact prefixLift 2108750
  have htrace : WordTrace (prefixWord ++ tailWord_2108750) baseStart_2108750 baseEnd_2108750 := by
    simpa [prefixWord, tailWord_2108750, baseEnd_2108750] using wordTrace_append hprefix tailTrace_2108750
  have hstable : (prefixWord ++ tailWord_2108750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108750).length < 2 ^ (prefixWord ++ tailWord_2108750).sum := by decide
  have hdescent : baseEnd_2108750 < baseStart_2108750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108800 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2108800 : Nat := 118140960795 + 2108800 * 2 ^ 59
def prefixEnd_2108800 : Nat := 4983230072969 + 3 ^ 40 * 2108800 * 2
def baseEnd_2108800 : Nat := 1082828004201454544001811

theorem tailTrace_2108800 : CollatzResearch.WordTrace tailWord_2108800 prefixEnd_2108800 1082828004201454544001811 := by
  unfold tailWord_2108800
  simp only [CollatzResearch.WordTrace]
  refine ⟨38457127380092614605877927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51276169840123486141170569 38457127380092614605877927)
  ·
    refine ⟨57685691070138921908816891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38457127380092614605877927 57685691070138921908816891)
    ·
      refine ⟨86528536605208382863225337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57685691070138921908816891 86528536605208382863225337)
      ·
        refine ⟨64896402453906287147419003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86528536605208382863225337 64896402453906287147419003)
        ·
          refine ⟨97344603680859430721128505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64896402453906287147419003 97344603680859430721128505)
          ·
            refine ⟨73008452760644573040846379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97344603680859430721128505 73008452760644573040846379)
            ·
              refine ⟨109512679140966859561269569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73008452760644573040846379 109512679140966859561269569)
              ·
                refine ⟨82134509355725144670952177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109512679140966859561269569 82134509355725144670952177)
                ·
                  refine ⟨61600882016793858503214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82134509355725144670952177 61600882016793858503214133)
                  ·
                    refine ⟨5775082689074424234676325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61600882016793858503214133 5775082689074424234676325)
                    ·
                      refine ⟨1082828004201454544001811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5775082689074424234676325 1082828004201454544001811)
                      ·
                        rfl

theorem cell23_2108800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2108800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108800 prefixEnd_2108800 := by exact prefixLift 2108800
  have htrace : WordTrace (prefixWord ++ tailWord_2108800) baseStart_2108800 baseEnd_2108800 := by
    simpa [prefixWord, tailWord_2108800, baseEnd_2108800] using wordTrace_append hprefix tailTrace_2108800
  have hstable : (prefixWord ++ tailWord_2108800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108800).length < 2 ^ (prefixWord ++ tailWord_2108800).sum := by decide
  have hdescent : baseEnd_2108800 < baseStart_2108800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108804 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_2108804 : Nat := 118140960795 + 2108804 * 2 ^ 59
def prefixEnd_2108804 : Nat := 4983230072969 + 3 ^ 40 * 2108804 * 2
def baseEnd_2108804 : Nat := 1082830058124072528351793

theorem tailTrace_2108804 : CollatzResearch.WordTrace tailWord_2108804 prefixEnd_2108804 1082830058124072528351793 := by
  unfold tailWord_2108804
  simp only [CollatzResearch.WordTrace]
  refine ⟨38457200326085368947450733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51276267101447158596600977 38457200326085368947450733)
  ·
    refine ⟨14421450122282013355294025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38457200326085368947450733 14421450122282013355294025)
    ·
      refine ⟨10816087591711510016470519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14421450122282013355294025 10816087591711510016470519)
      ·
        refine ⟨16224131387567265024705779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10816087591711510016470519 16224131387567265024705779)
        ·
          refine ⟨24336197081350897537058669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16224131387567265024705779 24336197081350897537058669)
          ·
            refine ⟨9126073905506586576397001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24336197081350897537058669 9126073905506586576397001)
            ·
              refine ⟨6844555429129939932297751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126073905506586576397001 6844555429129939932297751)
              ·
                refine ⟨10266833143694909898446627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844555429129939932297751 10266833143694909898446627)
                ·
                  refine ⟨15400249715542364847669941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10266833143694909898446627 15400249715542364847669941)
                  ·
                    refine ⟨1443773410832096704469057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15400249715542364847669941 1443773410832096704469057)
                    ·
                      refine ⟨1082830058124072528351793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443773410832096704469057 1082830058124072528351793)
                      ·
                        rfl

theorem cell23_2108804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_2108804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108804 prefixEnd_2108804 := by exact prefixLift 2108804
  have htrace : WordTrace (prefixWord ++ tailWord_2108804) baseStart_2108804 baseEnd_2108804 := by
    simpa [prefixWord, tailWord_2108804, baseEnd_2108804] using wordTrace_append hprefix tailTrace_2108804
  have hstable : (prefixWord ++ tailWord_2108804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108804).length < 2 ^ (prefixWord ++ tailWord_2108804).sum := by decide
  have hdescent : baseEnd_2108804 < baseStart_2108804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108817 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_2108817 : Nat := 118140960795 + 2108817 * 2 ^ 59
def prefixEnd_2108817 : Nat := 4983230072969 + 3 ^ 40 * 2108817 * 2
def baseEnd_2108817 : Nat := 1082836733372580977489233

theorem tailTrace_2108817 : CollatzResearch.WordTrace tailWord_2108817 prefixEnd_2108817 1082836733372580977489233 := by
  unfold tailWord_2108817
  simp only [CollatzResearch.WordTrace]
  refine ⟨76914874801123641115124705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51276583200749094076749803 76914874801123641115124705)
  ·
    refine ⟨57686156100842730836343529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76914874801123641115124705 57686156100842730836343529)
    ·
      refine ⟨43264617075632048127257647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57686156100842730836343529 43264617075632048127257647)
      ·
        refine ⟨64896925613448072190886471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43264617075632048127257647 64896925613448072190886471)
        ·
          refine ⟨97345388420172108286329707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64896925613448072190886471 97345388420172108286329707)
          ·
            refine ⟨146018082630258162429494561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97345388420172108286329707 146018082630258162429494561)
            ·
              refine ⟨109513561972693621822120921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146018082630258162429494561 109513561972693621822120921)
              ·
                refine ⟨82135171479520216366590691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109513561972693621822120921 82135171479520216366590691)
                ·
                  refine ⟨123202757219280324549886037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82135171479520216366590691 123202757219280324549886037)
                  ·
                    refine ⟨1443782311163441303318977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 123202757219280324549886037 1443782311163441303318977)
                    ·
                      refine ⟨1082836733372580977489233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443782311163441303318977 1082836733372580977489233)
                      ·
                        rfl

theorem cell23_2108817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_2108817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108817 prefixEnd_2108817 := by exact prefixLift 2108817
  have htrace : WordTrace (prefixWord ++ tailWord_2108817) baseStart_2108817 baseEnd_2108817 := by
    simpa [prefixWord, tailWord_2108817, baseEnd_2108817] using wordTrace_append hprefix tailTrace_2108817
  have hstable : (prefixWord ++ tailWord_2108817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108817).length < 2 ^ (prefixWord ++ tailWord_2108817).sum := by decide
  have hdescent : baseEnd_2108817 < baseStart_2108817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108867 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3]
def baseStart_2108867 : Nat := 118140960795 + 2108867 * 2 ^ 59
def prefixEnd_2108867 : Nat := 4983230072969 + 3 ^ 40 * 2108867 * 2
def baseEnd_2108867 : Nat := 1082862407405305781864003

theorem tailTrace_2108867 : CollatzResearch.WordTrace tailWord_2108867 prefixEnd_2108867 1082862407405305781864003 := by
  unfold tailWord_2108867
  simp only [CollatzResearch.WordTrace]
  refine ⟨76916698450942499654444855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51277798967294999769629903 76916698450942499654444855)
  ·
    refine ⟨115375047676413749481667283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76916698450942499654444855 115375047676413749481667283)
    ·
      refine ⟨173062571514620624222500925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115375047676413749481667283 173062571514620624222500925)
      ·
        refine ⟨64898464317982734083437847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173062571514620624222500925 64898464317982734083437847)
        ·
          refine ⟨97347696476974101125156771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64898464317982734083437847 97347696476974101125156771)
          ·
            refine ⟨146021544715461151687735157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97347696476974101125156771 146021544715461151687735157)
            ·
              refine ⟨13689519817074482970725171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146021544715461151687735157 13689519817074482970725171)
              ·
                refine ⟨20534279725611724456087757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13689519817074482970725171 20534279725611724456087757)
                ·
                  refine ⟨7700354897104396671032909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20534279725611724456087757 7700354897104396671032909)
                  ·
                    refine ⟨2887633086414148751637341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7700354897104396671032909 2887633086414148751637341)
                    ·
                      refine ⟨1082862407405305781864003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2887633086414148751637341 1082862407405305781864003)
                      ·
                        rfl

theorem cell23_2108867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_2108867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108867 prefixEnd_2108867 := by exact prefixLift 2108867
  have htrace : WordTrace (prefixWord ++ tailWord_2108867) baseStart_2108867 baseEnd_2108867 := by
    simpa [prefixWord, tailWord_2108867, baseEnd_2108867] using wordTrace_append hprefix tailTrace_2108867
  have hstable : (prefixWord ++ tailWord_2108867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108867).length < 2 ^ (prefixWord ++ tailWord_2108867).sum := by decide
  have hdescent : baseEnd_2108867 < baseStart_2108867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108868 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2108868 : Nat := 118140960795 + 2108868 * 2 ^ 59
def prefixEnd_2108868 : Nat := 4983230072969 + 3 ^ 40 * 2108868 * 2
def baseEnd_2108868 : Nat := 1082862920885960277951499

theorem tailTrace_2108868 : CollatzResearch.WordTrace tailWord_2108868 prefixEnd_2108868 1082862920885960277951499 := by
  unfold tailWord_2108868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38458367461969438412615629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51277823282625917883487505 38458367461969438412615629)
  ·
    refine ⟨14421887798238539404730861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38458367461969438412615629 14421887798238539404730861)
    ·
      refine ⟨5408207924339452276774073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14421887798238539404730861 5408207924339452276774073)
      ·
        refine ⟨4056155943254589207580555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5408207924339452276774073 4056155943254589207580555)
        ·
          refine ⟨6084233914881883811370833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056155943254589207580555 6084233914881883811370833)
          ·
            refine ⟨4563175436161412858528125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6084233914881883811370833 4563175436161412858528125)
            ·
              refine ⟨1711190788560529821948047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4563175436161412858528125 1711190788560529821948047)
              ·
                refine ⟨2566786182840794732922071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711190788560529821948047 2566786182840794732922071)
                ·
                  refine ⟨3850179274261192099383107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566786182840794732922071 3850179274261192099383107)
                  ·
                    refine ⟨5775268911391788149074661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850179274261192099383107 5775268911391788149074661)
                    ·
                      refine ⟨1082862920885960277951499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5775268911391788149074661 1082862920885960277951499)
                      ·
                        rfl

theorem cell23_2108868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2108868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108868 prefixEnd_2108868 := by exact prefixLift 2108868
  have htrace : WordTrace (prefixWord ++ tailWord_2108868) baseStart_2108868 baseEnd_2108868 := by
    simpa [prefixWord, tailWord_2108868, baseEnd_2108868] using wordTrace_append hprefix tailTrace_2108868
  have hstable : (prefixWord ++ tailWord_2108868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108868).length < 2 ^ (prefixWord ++ tailWord_2108868).sum := by decide
  have hdescent : baseEnd_2108868 < baseStart_2108868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108871 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_2108871 : Nat := 118140960795 + 2108871 * 2 ^ 59
def prefixEnd_2108871 : Nat := 4983230072969 + 3 ^ 40 * 2108871 * 2
def baseEnd_2108871 : Nat := 1082864461327923766213985

theorem tailTrace_2108871 : CollatzResearch.WordTrace tailWord_2108871 prefixEnd_2108871 1082864461327923766213985 := by
  unfold tailWord_2108871
  simp only [CollatzResearch.WordTrace]
  refine ⟨76916844342928008337590467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51277896228618672225060311 76916844342928008337590467)
  ·
    refine ⟨115375266514392012506385701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76916844342928008337590467 115375266514392012506385701)
    ·
      refine ⟨21632862471448502344947319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115375266514392012506385701 21632862471448502344947319)
      ·
        refine ⟨32449293707172753517420979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21632862471448502344947319 32449293707172753517420979)
        ·
          refine ⟨48673940560759130276131469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32449293707172753517420979 48673940560759130276131469)
          ·
            refine ⟨18252727710284673853549301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48673940560759130276131469 18252727710284673853549301)
            ·
              refine ⟨1711193222839188173770247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18252727710284673853549301 1711193222839188173770247)
              ·
                refine ⟨2566789834258782260655371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711193222839188173770247 2566789834258782260655371)
                ·
                  refine ⟨3850184751388173390983057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566789834258782260655371 3850184751388173390983057)
                  ·
                    refine ⟨2887638563541130043237293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3850184751388173390983057 2887638563541130043237293)
                    ·
                      refine ⟨1082864461327923766213985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2887638563541130043237293 1082864461327923766213985)
                      ·
                        rfl

theorem cell23_2108871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_2108871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108871 prefixEnd_2108871 := by exact prefixLift 2108871
  have htrace : WordTrace (prefixWord ++ tailWord_2108871) baseStart_2108871 baseEnd_2108871 := by
    simpa [prefixWord, tailWord_2108871, baseEnd_2108871] using wordTrace_append hprefix tailTrace_2108871
  have hstable : (prefixWord ++ tailWord_2108871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108871).length < 2 ^ (prefixWord ++ tailWord_2108871).sum := by decide
  have hdescent : baseEnd_2108871 < baseStart_2108871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108901 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2108901 : Nat := 118140960795 + 2108901 * 2 ^ 59
def prefixEnd_2108901 : Nat := 4983230072969 + 3 ^ 40 * 2108901 * 2
def baseEnd_2108901 : Nat := 1082879865747558648838847

theorem tailTrace_2108901 : CollatzResearch.WordTrace tailWord_2108901 prefixEnd_2108901 1082879865747558648838847 := by
  unfold tailWord_2108901
  simp only [CollatzResearch.WordTrace]
  refine ⟨76917938532819323461182557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51278625688546215640788371 76917938532819323461182557)
  ·
    refine ⟨28844226949807246297943459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76917938532819323461182557 28844226949807246297943459)
    ·
      refine ⟨43266340424710869446915189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28844226949807246297943459 43266340424710869446915189)
      ·
        refine ⟨4056219414816644010648299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43266340424710869446915189 4056219414816644010648299)
        ·
          refine ⟨6084329122224966015972449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056219414816644010648299 6084329122224966015972449)
          ·
            refine ⟨4563246841668724511979337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6084329122224966015972449 4563246841668724511979337)
            ·
              refine ⟨3422435131251543383984503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4563246841668724511979337 3422435131251543383984503)
              ·
                refine ⟨5133652696877315075976755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422435131251543383984503 5133652696877315075976755)
                ·
                  refine ⟨7700479045315972613965133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133652696877315075976755 7700479045315972613965133)
                  ·
                    refine ⟨2887679641993489730236925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7700479045315972613965133 2887679641993489730236925)
                    ·
                      refine ⟨1082879865747558648838847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2887679641993489730236925 1082879865747558648838847)
                      ·
                        rfl

theorem cell23_2108901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2108901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108901 prefixEnd_2108901 := by exact prefixLift 2108901
  have htrace : WordTrace (prefixWord ++ tailWord_2108901) baseStart_2108901 baseEnd_2108901 := by
    simpa [prefixWord, tailWord_2108901, baseEnd_2108901] using wordTrace_append hprefix tailTrace_2108901
  have hstable : (prefixWord ++ tailWord_2108901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108901).length < 2 ^ (prefixWord ++ tailWord_2108901).sum := by decide
  have hdescent : baseEnd_2108901 < baseStart_2108901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108927 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_2108927 : Nat := 118140960795 + 2108927 * 2 ^ 59
def prefixEnd_2108927 : Nat := 4983230072969 + 3 ^ 40 * 2108927 * 2
def baseEnd_2108927 : Nat := 1082893216244575547113727

theorem tailTrace_2108927 : CollatzResearch.WordTrace tailWord_2108927 prefixEnd_2108927 1082893216244575547113727 := by
  unfold tailWord_2108927
  simp only [CollatzResearch.WordTrace]
  refine ⟨76918886830725129901629035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51279257887150086601086023 76918886830725129901629035)
  ·
    refine ⟨115378330246087694852443553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76918886830725129901629035 115378330246087694852443553)
    ·
      refine ⟨86533747684565771139332665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115378330246087694852443553 86533747684565771139332665)
      ·
        refine ⟨64900310763424328354499499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86533747684565771139332665 64900310763424328354499499)
        ·
          refine ⟨97350466145136492531749249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64900310763424328354499499 97350466145136492531749249)
          ·
            refine ⟨73012849608852369398811937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97350466145136492531749249 73012849608852369398811937)
            ·
              refine ⟨54759637206639277049108953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73012849608852369398811937 54759637206639277049108953)
              ·
                refine ⟨41069727904979457786831715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54759637206639277049108953 41069727904979457786831715)
                ·
                  refine ⟨61604591857469186680247573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41069727904979457786831715 61604591857469186680247573)
                  ·
                    refine ⟨2887715243318868125636605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61604591857469186680247573 2887715243318868125636605)
                    ·
                      refine ⟨1082893216244575547113727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2887715243318868125636605 1082893216244575547113727)
                      ·
                        rfl

theorem cell23_2108927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_2108927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108927 prefixEnd_2108927 := by exact prefixLift 2108927
  have htrace : WordTrace (prefixWord ++ tailWord_2108927) baseStart_2108927 baseEnd_2108927 := by
    simpa [prefixWord, tailWord_2108927, baseEnd_2108927] using wordTrace_append hprefix tailTrace_2108927
  have hstable : (prefixWord ++ tailWord_2108927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108927).length < 2 ^ (prefixWord ++ tailWord_2108927).sum := by decide
  have hdescent : baseEnd_2108927 < baseStart_2108927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108937 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_2108937 : Nat := 118140960795 + 2108937 * 2 ^ 59
def prefixEnd_2108937 : Nat := 4983230072969 + 3 ^ 40 * 2108937 * 2
def baseEnd_2108937 : Nat := 1082898351051120507988681

theorem tailTrace_2108937 : CollatzResearch.WordTrace tailWord_2108937 prefixEnd_2108937 1082898351051120507988681 := by
  unfold tailWord_2108937
  simp only [CollatzResearch.WordTrace]
  refine ⟨76919251560688901609493065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51279501040459267739662043 76919251560688901609493065)
  ·
    refine ⟨57689438670516676207119799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76919251560688901609493065 57689438670516676207119799)
    ·
      refine ⟨86534158005775014310679699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57689438670516676207119799 86534158005775014310679699)
      ·
        refine ⟨129801237008662521466019549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86534158005775014310679699 129801237008662521466019549)
        ·
          refine ⟨48675463878248445549757331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129801237008662521466019549 48675463878248445549757331)
          ·
            refine ⟨73013195817372668324635997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48675463878248445549757331 73013195817372668324635997)
            ·
              refine ⟨27379948431514750621738499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73013195817372668324635997 27379948431514750621738499)
              ·
                refine ⟨41069922647272125932607749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27379948431514750621738499 41069922647272125932607749)
                ·
                  refine ⟨7700610496363523612363953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41069922647272125932607749 7700610496363523612363953)
                  ·
                    refine ⟨5775457872272642709272965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7700610496363523612363953 5775457872272642709272965)
                    ·
                      refine ⟨1082898351051120507988681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5775457872272642709272965 1082898351051120507988681)
                      ·
                        rfl

theorem cell23_2108937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_2108937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108937 prefixEnd_2108937 := by exact prefixLift 2108937
  have htrace : WordTrace (prefixWord ++ tailWord_2108937) baseStart_2108937 baseEnd_2108937 := by
    simpa [prefixWord, tailWord_2108937, baseEnd_2108937] using wordTrace_append hprefix tailTrace_2108937
  have hstable : (prefixWord ++ tailWord_2108937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108937).length < 2 ^ (prefixWord ++ tailWord_2108937).sum := by decide
  have hdescent : baseEnd_2108937 < baseStart_2108937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108947 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 7]
def baseStart_2108947 : Nat := 118140960795 + 2108947 * 2 ^ 59
def prefixEnd_2108947 : Nat := 4983230072969 + 3 ^ 40 * 2108947 * 2
def baseEnd_2108947 : Nat := 120322609539740607651515

theorem tailTrace_2108947 : CollatzResearch.WordTrace tailWord_2108947 prefixEnd_2108947 120322609539740607651515 := by
  unfold tailWord_2108947
  simp only [CollatzResearch.WordTrace]
  refine ⟨76919616290652673317357095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51279744193768448878238063 76919616290652673317357095)
  ·
    refine ⟨115379424435979009976035643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76919616290652673317357095 115379424435979009976035643)
    ·
      refine ⟨173069136653968514964053465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115379424435979009976035643 173069136653968514964053465)
      ·
        refine ⟨129801852490476386223040099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173069136653968514964053465 129801852490476386223040099)
        ·
          refine ⟨194702778735714579334560149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129801852490476386223040099 194702778735714579334560149)
          ·
            refine ⟨9126692753236620906307507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 194702778735714579334560149 9126692753236620906307507)
            ·
              refine ⟨13690039129854931359461261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9126692753236620906307507 13690039129854931359461261)
              ·
                refine ⟨5133764673695599259797973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13690039129854931359461261 5133764673695599259797973)
                ·
                  refine ⟨120322609539740607651515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5133764673695599259797973 120322609539740607651515)
                  ·
                    rfl

theorem cell23_2108947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 7].length) (baseStart_2108947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108947 prefixEnd_2108947 := by exact prefixLift 2108947
  have htrace : WordTrace (prefixWord ++ tailWord_2108947) baseStart_2108947 baseEnd_2108947 := by
    simpa [prefixWord, tailWord_2108947, baseEnd_2108947] using wordTrace_append hprefix tailTrace_2108947
  have hstable : (prefixWord ++ tailWord_2108947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108947).length < 2 ^ (prefixWord ++ tailWord_2108947).sum := by decide
  have hdescent : baseEnd_2108947 < baseStart_2108947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108981 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 5]
def baseStart_2108981 : Nat := 118140960795 + 2108981 * 2 ^ 59
def prefixEnd_2108981 : Nat := 4983230072969 + 3 ^ 40 * 2108981 * 2
def baseEnd_2108981 : Nat := 120324549355546481759831

theorem tailTrace_2108981 : CollatzResearch.WordTrace tailWord_2108981 prefixEnd_2108981 120324549355546481759831 := by
  unfold tailWord_2108981
  simp only [CollatzResearch.WordTrace]
  refine ⟨76920856372529497124094797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51280570915019664749396531 76920856372529497124094797)
  ·
    refine ⟨28845321139698561421535549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76920856372529497124094797 28845321139698561421535549)
    ·
      refine ⟨10816995427386960533075831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28845321139698561421535549 10816995427386960533075831)
      ·
        refine ⟨16225493141080440799613747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10816995427386960533075831 16225493141080440799613747)
        ·
          refine ⟨24338239711620661199420621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16225493141080440799613747 24338239711620661199420621)
          ·
            refine ⟨9126839891857747949782733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24338239711620661199420621 9126839891857747949782733)
            ·
              refine ⟨3422564959446655481168525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9126839891857747949782733 3422564959446655481168525)
              ·
                refine ⟨1283461859792495805438197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3422564959446655481168525 1283461859792495805438197)
                ·
                  refine ⟨120324549355546481759831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283461859792495805438197 120324549355546481759831)
                  ·
                    rfl

theorem cell23_2108981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_2108981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2108981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2108981 prefixEnd_2108981 := by exact prefixLift 2108981
  have htrace : WordTrace (prefixWord ++ tailWord_2108981) baseStart_2108981 baseEnd_2108981 := by
    simpa [prefixWord, tailWord_2108981, baseEnd_2108981] using wordTrace_append hprefix tailTrace_2108981
  have hstable : (prefixWord ++ tailWord_2108981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108981).length < 2 ^ (prefixWord ++ tailWord_2108981).sum := by decide
  have hdescent : baseEnd_2108981 < baseStart_2108981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109004 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2109004 : Nat := 118140960795 + 2109004 * 2 ^ 59
def prefixEnd_2109004 : Nat := 4983230072969 + 3 ^ 40 * 2109004 * 2
def baseEnd_2109004 : Nat := 1082932754254971745850873

theorem tailTrace_2109004 : CollatzResearch.WordTrace tailWord_2109004 prefixEnd_2109004 1082932754254971745850873 := by
  unfold tailWord_2109004
  simp only [CollatzResearch.WordTrace]
  refine ⟨38460847625723086026091033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51281130167630781368121377 38460847625723086026091033)
  ·
    refine ⟨28845635719292314519568275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38460847625723086026091033 28845635719292314519568275)
    ·
      refine ⟨43268453578938471779352413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28845635719292314519568275 43268453578938471779352413)
      ·
        refine ⟨16225670092101926917257155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43268453578938471779352413 16225670092101926917257155)
        ·
          refine ⟨24338505138152890375885733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16225670092101926917257155 24338505138152890375885733)
          ·
            refine ⟨4563469713403666945478575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24338505138152890375885733 4563469713403666945478575)
            ·
              refine ⟨6845204570105500418217863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563469713403666945478575 6845204570105500418217863)
              ·
                refine ⟨10267806855158250627326795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6845204570105500418217863 10267806855158250627326795)
                ·
                  refine ⟨15401710282737375940990193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10267806855158250627326795 15401710282737375940990193)
                  ·
                    refine ⟨11551282712053031955742645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15401710282737375940990193 11551282712053031955742645)
                    ·
                      refine ⟨1082932754254971745850873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11551282712053031955742645 1082932754254971745850873)
                      ·
                        rfl

theorem cell23_2109004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2109004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109004 prefixEnd_2109004 := by exact prefixLift 2109004
  have htrace : WordTrace (prefixWord ++ tailWord_2109004) baseStart_2109004 baseEnd_2109004 := by
    simpa [prefixWord, tailWord_2109004, baseEnd_2109004] using wordTrace_append hprefix tailTrace_2109004
  have hstable : (prefixWord ++ tailWord_2109004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109004).length < 2 ^ (prefixWord ++ tailWord_2109004).sum := by decide
  have hdescent : baseEnd_2109004 < baseStart_2109004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109017 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_2109017 : Nat := 118140960795 + 2109017 * 2 ^ 59
def prefixEnd_2109017 : Nat := 4983230072969 + 3 ^ 40 * 2109017 * 2
def baseEnd_2109017 : Nat := 1082939429503480194988313

theorem tailTrace_2109017 : CollatzResearch.WordTrace tailWord_2109017 prefixEnd_2109017 1082939429503480194988313 := by
  unfold tailWord_2109017
  simp only [CollatzResearch.WordTrace]
  refine ⟨76922169400399075272405305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51281446266932716848270203 76922169400399075272405305)
  ·
    refine ⟨57691627050299306454303979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76922169400399075272405305 57691627050299306454303979)
    ·
      refine ⟨86537440575448959681455969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57691627050299306454303979 86537440575448959681455969)
      ·
        refine ⟨64903080431586719761091977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86537440575448959681455969 64903080431586719761091977)
        ·
          refine ⟨48677310323690039820818983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64903080431586719761091977 48677310323690039820818983)
          ·
            refine ⟨73015965485535059731228475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48677310323690039820818983 73015965485535059731228475)
            ·
              refine ⟨109523948228302589596842713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73015965485535059731228475 109523948228302589596842713)
              ·
                refine ⟨82142961171226942197632035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109523948228302589596842713 82142961171226942197632035)
                ·
                  refine ⟨123214441756840413296448053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82142961171226942197632035 123214441756840413296448053)
                  ·
                    refine ⟨11551353914703788746542005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123214441756840413296448053 11551353914703788746542005)
                    ·
                      refine ⟨1082939429503480194988313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11551353914703788746542005 1082939429503480194988313)
                      ·
                        rfl

theorem cell23_2109017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_2109017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109017 prefixEnd_2109017 := by exact prefixLift 2109017
  have htrace : WordTrace (prefixWord ++ tailWord_2109017) baseStart_2109017 baseEnd_2109017 := by
    simpa [prefixWord, tailWord_2109017, baseEnd_2109017] using wordTrace_append hprefix tailTrace_2109017
  have hstable : (prefixWord ++ tailWord_2109017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109017).length < 2 ^ (prefixWord ++ tailWord_2109017).sum := by decide
  have hdescent : baseEnd_2109017 < baseStart_2109017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109024 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_2109024 : Nat := 118140960795 + 2109024 * 2 ^ 59
def prefixEnd_2109024 : Nat := 4983230072969 + 3 ^ 40 * 2109024 * 2
def baseEnd_2109024 : Nat := 360981007956020555866927

theorem tailTrace_2109024 : CollatzResearch.WordTrace tailWord_2109024 prefixEnd_2109024 360981007956020555866927 := by
  unfold tailWord_2109024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38461212355686857733955063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51281616474249143645273417 38461212355686857733955063)
  ·
    refine ⟨57691818533530286600932595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38461212355686857733955063 57691818533530286600932595)
    ·
      refine ⟨86537727800295429901398893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57691818533530286600932595 86537727800295429901398893)
      ·
        refine ⟨32451647925110786213024585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86537727800295429901398893 32451647925110786213024585)
        ·
          refine ⟨24338735943833089659768439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32451647925110786213024585 24338735943833089659768439)
          ·
            refine ⟨36508103915749634489652659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24338735943833089659768439 36508103915749634489652659)
            ·
              refine ⟨54762155873624451734478989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36508103915749634489652659 54762155873624451734478989)
              ·
                refine ⟨20535808452609169400429621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54762155873624451734478989 20535808452609169400429621)
                ·
                  refine ⟨1925232042432109631290277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20535808452609169400429621 1925232042432109631290277)
                  ·
                    refine ⟨360981007956020555866927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925232042432109631290277 360981007956020555866927)
                    ·
                      rfl

theorem cell23_2109024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_2109024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109024 prefixEnd_2109024 := by exact prefixLift 2109024
  have htrace : WordTrace (prefixWord ++ tailWord_2109024) baseStart_2109024 baseEnd_2109024 := by
    simpa [prefixWord, tailWord_2109024, baseEnd_2109024] using wordTrace_append hprefix tailTrace_2109024
  have hstable : (prefixWord ++ tailWord_2109024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109024).length < 2 ^ (prefixWord ++ tailWord_2109024).sum := by decide
  have hdescent : baseEnd_2109024 < baseStart_2109024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109091 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 5, 2]
def baseStart_2109091 : Nat := 118140960795 + 2109091 * 2 ^ 59
def prefixEnd_2109091 : Nat := 4983230072969 + 3 ^ 40 * 2109091 * 2
def baseEnd_2109091 : Nat := 1082977427071912905462973

theorem tailTrace_2109091 : CollatzResearch.WordTrace tailWord_2109091 prefixEnd_2109091 1082977427071912905462973 := by
  unfold tailWord_2109091
  simp only [CollatzResearch.WordTrace]
  refine ⟨76924868402130985910599127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51283245601420657273732751 76924868402130985910599127)
  ·
    refine ⟨115387302603196478865898691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76924868402130985910599127 115387302603196478865898691)
    ·
      refine ⟨173080953904794718298848037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115387302603196478865898691 173080953904794718298848037)
      ·
        refine ⟨32452678857149009681034007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173080953904794718298848037 32452678857149009681034007)
        ·
          refine ⟨48679018285723514521551011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32452678857149009681034007 48679018285723514521551011)
          ·
            refine ⟨73018527428585271782326517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48679018285723514521551011 73018527428585271782326517)
            ·
              refine ⟨6845486946429869229593111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73018527428585271782326517 6845486946429869229593111)
              ·
                refine ⟨10268230419644803844389667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6845486946429869229593111 10268230419644803844389667)
                ·
                  refine ⟨15402345629467205766584501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10268230419644803844389667 15402345629467205766584501)
                  ·
                    refine ⟨1443969902762550540617297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15402345629467205766584501 1443969902762550540617297)
                    ·
                      refine ⟨1082977427071912905462973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1443969902762550540617297 1082977427071912905462973)
                      ·
                        rfl

theorem cell23_2109091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_2109091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109091 prefixEnd_2109091 := by exact prefixLift 2109091
  have htrace : WordTrace (prefixWord ++ tailWord_2109091) baseStart_2109091 baseEnd_2109091 := by
    simpa [prefixWord, tailWord_2109091, baseEnd_2109091] using wordTrace_append hprefix tailTrace_2109091
  have hstable : (prefixWord ++ tailWord_2109091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109091).length < 2 ^ (prefixWord ++ tailWord_2109091).sum := by decide
  have hdescent : baseEnd_2109091 < baseStart_2109091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109131 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 2, 4]
def baseStart_2109131 : Nat := 118140960795 + 2109131 * 2 ^ 59
def prefixEnd_2109131 : Nat := 4983230072969 + 3 ^ 40 * 2109131 * 2
def baseEnd_2109131 : Nat := 360999322099364249654263

theorem tailTrace_2109131 : CollatzResearch.WordTrace tailWord_2109131 prefixEnd_2109131 360999322099364249654263 := by
  unfold tailWord_2109131
  simp only [CollatzResearch.WordTrace]
  refine ⟨76926327321986072742055247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51284218214657381828036831 76926327321986072742055247)
  ·
    refine ⟨115389490982979109113082871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76926327321986072742055247 115389490982979109113082871)
    ·
      refine ⟨173084236474468663669624307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115389490982979109113082871 173084236474468663669624307)
      ·
        refine ⟨259626354711702995504436461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173084236474468663669624307 259626354711702995504436461)
        ·
          refine ⟨97359883016888623314163673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259626354711702995504436461 97359883016888623314163673)
          ·
            refine ⟨73019912262666467485622755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97359883016888623314163673 73019912262666467485622755)
            ·
              refine ⟨109529868393999701228434133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73019912262666467485622755 109529868393999701228434133)
              ·
                refine ⟨2567106290484367997541425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109529868393999701228434133 2567106290484367997541425)
                ·
                  refine ⟨1925329717863275998156069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567106290484367997541425 1925329717863275998156069)
                  ·
                    refine ⟨360999322099364249654263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925329717863275998156069 360999322099364249654263)
                    ·
                      rfl

theorem cell23_2109131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 4].length) (baseStart_2109131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109131 prefixEnd_2109131 := by exact prefixLift 2109131
  have htrace : WordTrace (prefixWord ++ tailWord_2109131) baseStart_2109131 baseEnd_2109131 := by
    simpa [prefixWord, tailWord_2109131, baseEnd_2109131] using wordTrace_append hprefix tailTrace_2109131
  have hstable : (prefixWord ++ tailWord_2109131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109131).length < 2 ^ (prefixWord ++ tailWord_2109131).sum := by decide
  have hdescent : baseEnd_2109131 < baseStart_2109131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109138 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2109138 : Nat := 118140960795 + 2109138 * 2 ^ 59
def prefixEnd_2109138 : Nat := 4983230072969 + 3 ^ 40 * 2109138 * 2
def baseEnd_2109138 : Nat := 1083001560662674221575257

theorem tailTrace_2109138 : CollatzResearch.WordTrace tailWord_2109138 prefixEnd_2109138 1083001560662674221575257 := by
  unfold tailWord_2109138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19231645658240178234390017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51284388421973808625040045 19231645658240178234390017)
  ·
    refine ⟨14423734243680133675792513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19231645658240178234390017 14423734243680133675792513)
    ·
      refine ⟨10817800682760100256844385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14423734243680133675792513 10817800682760100256844385)
      ·
        refine ⟨8113350512070075192633289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10817800682760100256844385 8113350512070075192633289)
        ·
          refine ⟨6085012884052556394474967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8113350512070075192633289 6085012884052556394474967)
          ·
            refine ⟨9127519326078834591712451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6085012884052556394474967 9127519326078834591712451)
            ·
              refine ⟨13691278989118251887568677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127519326078834591712451 13691278989118251887568677)
              ·
                refine ⟨2567114810459672228919127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13691278989118251887568677 2567114810459672228919127)
                ·
                  refine ⟨3850672215689508343378691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567114810459672228919127 3850672215689508343378691)
                  ·
                    refine ⟨5776008323534262515068037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3850672215689508343378691 5776008323534262515068037)
                    ·
                      refine ⟨1083001560662674221575257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5776008323534262515068037 1083001560662674221575257)
                      ·
                        rfl

theorem cell23_2109138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2109138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109138 prefixEnd_2109138 := by exact prefixLift 2109138
  have htrace : WordTrace (prefixWord ++ tailWord_2109138) baseStart_2109138 baseEnd_2109138 := by
    simpa [prefixWord, tailWord_2109138, baseEnd_2109138] using wordTrace_append hprefix tailTrace_2109138
  have hstable : (prefixWord ++ tailWord_2109138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109138).length < 2 ^ (prefixWord ++ tailWord_2109138).sum := by decide
  have hdescent : baseEnd_2109138 < baseStart_2109138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109144 : List Nat := [2, 1, 2, 2, 3, 1, 3, 9]
def baseStart_2109144 : Nat := 118140960795 + 2109144 * 2 ^ 59
def prefixEnd_2109144 : Nat := 4983230072969 + 3 ^ 40 * 2109144 * 2
def baseEnd_2109144 : Nat := 40111283020244488818527

theorem tailTrace_2109144 : CollatzResearch.WordTrace tailWord_2109144 prefixEnd_2109144 40111283020244488818527 := by
  unfold tailWord_2109144
  simp only [CollatzResearch.WordTrace]
  refine ⟨38463400735469487981139243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51284534313959317308185657 38463400735469487981139243)
  ·
    refine ⟨57695101103204231971708865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38463400735469487981139243 57695101103204231971708865)
    ·
      refine ⟨43271325827403173978781649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57695101103204231971708865 43271325827403173978781649)
      ·
        refine ⟨32453494370552380484086237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43271325827403173978781649 32453494370552380484086237)
        ·
          refine ⟨12170060388957142681532339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32453494370552380484086237 12170060388957142681532339)
          ·
            refine ⟨18255090583435714022298509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12170060388957142681532339 18255090583435714022298509)
            ·
              refine ⟨6845658968788392758361941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18255090583435714022298509 6845658968788392758361941)
              ·
                refine ⟨40111283020244488818527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6845658968788392758361941 40111283020244488818527)
                ·
                  rfl

theorem cell23_2109144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 9].length) (baseStart_2109144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109144 prefixEnd_2109144 := by exact prefixLift 2109144
  have htrace : WordTrace (prefixWord ++ tailWord_2109144) baseStart_2109144 baseEnd_2109144 := by
    simpa [prefixWord, tailWord_2109144, baseEnd_2109144] using wordTrace_append hprefix tailTrace_2109144
  have hstable : (prefixWord ++ tailWord_2109144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109144).length < 2 ^ (prefixWord ++ tailWord_2109144).sum := by decide
  have hdescent : baseEnd_2109144 < baseStart_2109144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109184 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2109184 : Nat := 118140960795 + 2109184 * 2 ^ 59
def prefixEnd_2109184 : Nat := 4983230072969 + 3 ^ 40 * 2109184 * 2
def baseEnd_2109184 : Nat := 1083025180772781041600045

theorem tailTrace_2109184 : CollatzResearch.WordTrace tailWord_2109184 prefixEnd_2109184 1083025180772781041600045 := by
  unfold tailWord_2109184
  simp only [CollatzResearch.WordTrace]
  refine ⟨38464130195397031396867303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51285506927196041862489737 38464130195397031396867303)
  ·
    refine ⟨57696195293095547095300955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38464130195397031396867303 57696195293095547095300955)
    ·
      refine ⟨86544292939643320642951433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57696195293095547095300955 86544292939643320642951433)
      ·
        refine ⟨64908219704732490482213575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86544292939643320642951433 64908219704732490482213575)
        ·
          refine ⟨97362329557098735723320363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64908219704732490482213575 97362329557098735723320363)
          ·
            refine ⟨146043494335648103584980545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97362329557098735723320363 146043494335648103584980545)
            ·
              refine ⟨109532620751736077688735409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146043494335648103584980545 109532620751736077688735409)
              ·
                refine ⟨82149465563802058266551557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109532620751736077688735409 82149465563802058266551557)
                ·
                  refine ⟨15403024793212885924978417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82149465563802058266551557 15403024793212885924978417)
                  ·
                    refine ⟨11552268594909664443733813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15403024793212885924978417 11552268594909664443733813)
                    ·
                      refine ⟨1083025180772781041600045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11552268594909664443733813 1083025180772781041600045)
                      ·
                        rfl

theorem cell23_2109184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2109184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109184 prefixEnd_2109184 := by exact prefixLift 2109184
  have htrace : WordTrace (prefixWord ++ tailWord_2109184) baseStart_2109184 baseEnd_2109184 := by
    simpa [prefixWord, tailWord_2109184, baseEnd_2109184] using wordTrace_append hprefix tailTrace_2109184
  have hstable : (prefixWord ++ tailWord_2109184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109184).length < 2 ^ (prefixWord ++ tailWord_2109184).sum := by decide
  have hdescent : baseEnd_2109184 < baseStart_2109184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109238 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2109238 : Nat := 118140960795 + 2109238 * 2 ^ 59
def prefixEnd_2109238 : Nat := 4983230072969 + 3 ^ 40 * 2109238 * 2
def baseEnd_2109238 : Nat := 361017636242707943441599

theorem tailTrace_2109238 : CollatzResearch.WordTrace tailWord_2109238 prefixEnd_2109238 361017636242707943441599 := by
  unfold tailWord_2109238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808139370787401876012523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51286819955065620010800245 4808139370787401876012523)
  ·
    refine ⟨7212209056181102814018785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808139370787401876012523 7212209056181102814018785)
    ·
      refine ⟨5409156792135827110514089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7212209056181102814018785 5409156792135827110514089)
      ·
        refine ⟨4056867594101870332885567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5409156792135827110514089 4056867594101870332885567)
        ·
          refine ⟨6085301391152805499328351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056867594101870332885567 6085301391152805499328351)
          ·
            refine ⟨9127952086729208248992527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6085301391152805499328351 9127952086729208248992527)
            ·
              refine ⟨13691928130093812373488791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127952086729208248992527 13691928130093812373488791)
              ·
                refine ⟨20537892195140718560233187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13691928130093812373488791 20537892195140718560233187)
                ·
                  refine ⟨30806838292711077840349781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20537892195140718560233187 30806838292711077840349781)
                  ·
                    refine ⟨361017636242707943441599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30806838292711077840349781 361017636242707943441599)
                    ·
                      rfl

theorem cell23_2109238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2109238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109238 prefixEnd_2109238 := by exact prefixLift 2109238
  have htrace : WordTrace (prefixWord ++ tailWord_2109238) baseStart_2109238 baseEnd_2109238 := by
    simpa [prefixWord, tailWord_2109238, baseEnd_2109238] using wordTrace_append hprefix tailTrace_2109238
  have hstable : (prefixWord ++ tailWord_2109238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109238).length < 2 ^ (prefixWord ++ tailWord_2109238).sum := by decide
  have hdescent : baseEnd_2109238 < baseStart_2109238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109245 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2109245 : Nat := 118140960795 + 2109245 * 2 ^ 59
def prefixEnd_2109245 : Nat := 4983230072969 + 3 ^ 40 * 2109245 * 2
def baseEnd_2109245 : Nat := 1083056503092705302937265

theorem tailTrace_2109245 : CollatzResearch.WordTrace tailWord_2109245 prefixEnd_2109245 1083056503092705302937265 := by
  unfold tailWord_2109245
  simp only [CollatzResearch.WordTrace]
  refine ⟨76930485243573070211705189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51286990162382046807803459 76930485243573070211705189)
  ·
    refine ⟨14424465983169950664694723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76930485243573070211705189 14424465983169950664694723)
    ·
      refine ⟨21636698974754925997042085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14424465983169950664694723 21636698974754925997042085)
      ·
        refine ⟨4056881057766548624445391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21636698974754925997042085 4056881057766548624445391)
        ·
          refine ⟨6085321586649822936668087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056881057766548624445391 6085321586649822936668087)
          ·
            refine ⟨9127982379974734405002131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6085321586649822936668087 9127982379974734405002131)
            ·
              refine ⟨13691973569962101607503197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127982379974734405002131 13691973569962101607503197)
              ·
                refine ⟨5134490088735788102813699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13691973569962101607503197 5134490088735788102813699)
                ·
                  refine ⟨7701735133103682154220549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5134490088735788102813699 7701735133103682154220549)
                  ·
                    refine ⟨1444075337456940403916353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7701735133103682154220549 1444075337456940403916353)
                    ·
                      refine ⟨1083056503092705302937265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444075337456940403916353 1083056503092705302937265)
                      ·
                        rfl

theorem cell23_2109245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2109245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109245 prefixEnd_2109245 := by exact prefixLift 2109245
  have htrace : WordTrace (prefixWord ++ tailWord_2109245) baseStart_2109245 baseEnd_2109245 := by
    simpa [prefixWord, tailWord_2109245, baseEnd_2109245] using wordTrace_append hprefix tailTrace_2109245
  have hstable : (prefixWord ++ tailWord_2109245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109245).length < 2 ^ (prefixWord ++ tailWord_2109245).sum := by decide
  have hdescent : baseEnd_2109245 < baseStart_2109245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109251 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 7]
def baseStart_2109251 : Nat := 118140960795 + 2109251 * 2 ^ 59
def prefixEnd_2109251 : Nat := 4983230072969 + 3 ^ 40 * 2109251 * 2
def baseEnd_2109251 : Nat := 120339953775181364384693

theorem tailTrace_2109251 : CollatzResearch.WordTrace tailWord_2109251 prefixEnd_2109251 120339953775181364384693 := by
  unfold tailWord_2109251
  simp only [CollatzResearch.WordTrace]
  refine ⟨76930704081551333236423607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51287136054367555490949071 76930704081551333236423607)
  ·
    refine ⟨115396056122326999854635411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76930704081551333236423607 115396056122326999854635411)
    ·
      refine ⟨173094084183490499781953117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115396056122326999854635411 173094084183490499781953117)
      ·
        refine ⟨64910281568808937418232419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173094084183490499781953117 64910281568808937418232419)
        ·
          refine ⟨97365422353213406127348629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64910281568808937418232419 97365422353213406127348629)
          ·
            refine ⟨4564004172806878412219467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97365422353213406127348629 4564004172806878412219467)
            ·
              refine ⟨6846006259210317618329201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564004172806878412219467 6846006259210317618329201)
              ·
                refine ⟨5134504694407738213746901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6846006259210317618329201 5134504694407738213746901)
                ·
                  refine ⟨120339953775181364384693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5134504694407738213746901 120339953775181364384693)
                  ·
                    rfl

theorem cell23_2109251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 7].length) (baseStart_2109251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109251 prefixEnd_2109251 := by exact prefixLift 2109251
  have htrace : WordTrace (prefixWord ++ tailWord_2109251) baseStart_2109251 baseEnd_2109251 := by
    simpa [prefixWord, tailWord_2109251, baseEnd_2109251] using wordTrace_append hprefix tailTrace_2109251
  have hstable : (prefixWord ++ tailWord_2109251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109251).length < 2 ^ (prefixWord ++ tailWord_2109251).sum := by decide
  have hdescent : baseEnd_2109251 < baseStart_2109251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109281 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2109281 : Nat := 118140960795 + 2109281 * 2 ^ 59
def prefixEnd_2109281 : Nat := 4983230072969 + 3 ^ 40 * 2109281 * 2
def baseEnd_2109281 : Nat := 361024996132089054029033

theorem tailTrace_2109281 : CollatzResearch.WordTrace tailWord_2109281 prefixEnd_2109281 361024996132089054029033 := by
  unfold tailWord_2109281
  simp only [CollatzResearch.WordTrace]
  refine ⟨76931798271442648360015697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51287865514295098906677131 76931798271442648360015697)
  ·
    refine ⟨57698848703581986270011773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76931798271442648360015697 57698848703581986270011773)
    ·
      refine ⟨21637068263843244851254415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57698848703581986270011773 21637068263843244851254415)
      ·
        refine ⟨32455602395764867276881623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21637068263843244851254415 32455602395764867276881623)
        ·
          refine ⟨48683403593647300915322435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32455602395764867276881623 48683403593647300915322435)
          ·
            refine ⟨73025105390470951372983653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48683403593647300915322435 73025105390470951372983653)
            ·
              refine ⟨13692207260713303382434435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73025105390470951372983653 13692207260713303382434435)
              ·
                refine ⟨20538310891069955073651653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13692207260713303382434435 20538310891069955073651653)
                ·
                  refine ⟨3850933292075616576309685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20538310891069955073651653 3850933292075616576309685)
                  ·
                    refine ⟨361024996132089054029033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3850933292075616576309685 361024996132089054029033)
                    ·
                      rfl

theorem cell23_2109281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2109281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109281 prefixEnd_2109281 := by exact prefixLift 2109281
  have htrace : WordTrace (prefixWord ++ tailWord_2109281) baseStart_2109281 baseEnd_2109281 := by
    simpa [prefixWord, tailWord_2109281, baseEnd_2109281] using wordTrace_append hprefix tailTrace_2109281
  have hstable : (prefixWord ++ tailWord_2109281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109281).length < 2 ^ (prefixWord ++ tailWord_2109281).sum := by decide
  have hdescent : baseEnd_2109281 < baseStart_2109281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109342 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2109342 : Nat := 118140960795 + 2109342 * 2 ^ 59
def prefixEnd_2109342 : Nat := 4983230072969 + 3 ^ 40 * 2109342 * 2
def baseEnd_2109342 : Nat := 1083106310716191423424319

theorem tailTrace_2109342 : CollatzResearch.WordTrace tailWord_2109342 prefixEnd_2109342 1083106310716191423424319 := by
  unfold tailWord_2109342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9616752890527706972248285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51289348749481103851990853 9616752890527706972248285)
  ·
    refine ⟨3606282333947890114593107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9616752890527706972248285 3606282333947890114593107)
    ·
      refine ⟨5409423500921835171889661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3606282333947890114593107 5409423500921835171889661)
      ·
        refine ⟨2028533812845688189458623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5409423500921835171889661 2028533812845688189458623)
        ·
          refine ⟨3042800719268532284187935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028533812845688189458623 3042800719268532284187935)
          ·
            refine ⟨4564201078902798426281903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042800719268532284187935 4564201078902798426281903)
            ·
              refine ⟨6846301618354197639422855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564201078902798426281903 6846301618354197639422855)
              ·
                refine ⟨10269452427531296459134283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6846301618354197639422855 10269452427531296459134283)
                ·
                  refine ⟨15404178641296944688701425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10269452427531296459134283 15404178641296944688701425)
                  ·
                    refine ⟨11553133980972708516526069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15404178641296944688701425 11553133980972708516526069)
                    ·
                      refine ⟨1083106310716191423424319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11553133980972708516526069 1083106310716191423424319)
                      ·
                        rfl

theorem cell23_2109342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2109342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109342 prefixEnd_2109342 := by exact prefixLift 2109342
  have htrace : WordTrace (prefixWord ++ tailWord_2109342) baseStart_2109342 baseEnd_2109342 := by
    simpa [prefixWord, tailWord_2109342, baseEnd_2109342] using wordTrace_append hprefix tailTrace_2109342
  have hstable : (prefixWord ++ tailWord_2109342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109342).length < 2 ^ (prefixWord ++ tailWord_2109342).sum := by decide
  have hdescent : baseEnd_2109342 < baseStart_2109342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109381 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_2109381 : Nat := 118140960795 + 2109381 * 2 ^ 59
def prefixEnd_2109381 : Nat := 4983230072969 + 3 ^ 40 * 2109381 * 2
def baseEnd_2109381 : Nat := 1083126336461716770836639

theorem tailTrace_2109381 : CollatzResearch.WordTrace tailWord_2109381 prefixEnd_2109381 1083126336461716770836639 := by
  unfold tailWord_2109381
  simp only [CollatzResearch.WordTrace]
  refine ⟨76935445571080365438655997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51290297047386910292437331 76935445571080365438655997)
  ·
    refine ⟨28850792089155137039495999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76935445571080365438655997 28850792089155137039495999)
    ·
      refine ⟨43276188133732705559243999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28850792089155137039495999 43276188133732705559243999)
      ·
        refine ⟨64914282200599058338865999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43276188133732705559243999 64914282200599058338865999)
        ·
          refine ⟨97371423300898587508298999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64914282200599058338865999 97371423300898587508298999)
          ·
            refine ⟨146057134951347881262448499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97371423300898587508298999 146057134951347881262448499)
            ·
              refine ⟨219085702427021821893672749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146057134951347881262448499 219085702427021821893672749)
              ·
                refine ⟨82157138410133183210127281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219085702427021821893672749 82157138410133183210127281)
                ·
                  refine ⟨61617853807599887407595461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82157138410133183210127281 61617853807599887407595461)
                  ·
                    refine ⟨11553347588924978888924149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61617853807599887407595461 11553347588924978888924149)
                    ·
                      refine ⟨1083126336461716770836639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11553347588924978888924149 1083126336461716770836639)
                      ·
                        rfl

theorem cell23_2109381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_2109381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109381 prefixEnd_2109381 := by exact prefixLift 2109381
  have htrace : WordTrace (prefixWord ++ tailWord_2109381) baseStart_2109381 baseEnd_2109381 := by
    simpa [prefixWord, tailWord_2109381, baseEnd_2109381] using wordTrace_append hprefix tailTrace_2109381
  have hstable : (prefixWord ++ tailWord_2109381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109381).length < 2 ^ (prefixWord ++ tailWord_2109381).sum := by decide
  have hdescent : baseEnd_2109381 < baseStart_2109381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109453 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2109453 : Nat := 118140960795 + 2109453 * 2 ^ 59
def prefixEnd_2109453 : Nat := 4983230072969 + 3 ^ 40 * 2109453 * 2
def baseEnd_2109453 : Nat := 1083163307068840489136309

theorem tailTrace_2109453 : CollatzResearch.WordTrace tailWord_2109453 prefixEnd_2109453 1083163307068840489136309 := by
  unfold tailWord_2109453
  simp only [CollatzResearch.WordTrace]
  refine ⟨76938071626819521735277013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51292047751213014490184675 76938071626819521735277013)
  ·
    refine ⟨1803236053753582540670555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 76938071626819521735277013 1803236053753582540670555)
    ·
      refine ⟨2704854080630373811005833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1803236053753582540670555 2704854080630373811005833)
      ·
        refine ⟨2028640560472780358254375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704854080630373811005833 2028640560472780358254375)
        ·
          refine ⟨3042960840709170537381563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028640560472780358254375 3042960840709170537381563)
          ·
            refine ⟨4564441261063755806072345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042960840709170537381563 4564441261063755806072345)
            ·
              refine ⟨3423330945797816854554259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4564441261063755806072345 3423330945797816854554259)
              ·
                refine ⟨5134996418696725281831389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423330945797816854554259 5134996418696725281831389)
                ·
                  refine ⟨1925623657011271980686771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5134996418696725281831389 1925623657011271980686771)
                  ·
                    refine ⟨2888435485516907971030157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1925623657011271980686771 2888435485516907971030157)
                    ·
                      refine ⟨1083163307068840489136309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2888435485516907971030157 1083163307068840489136309)
                      ·
                        rfl

theorem cell23_2109453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2109453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109453 prefixEnd_2109453 := by exact prefixLift 2109453
  have htrace : WordTrace (prefixWord ++ tailWord_2109453) baseStart_2109453 baseEnd_2109453 := by
    simpa [prefixWord, tailWord_2109453, baseEnd_2109453] using wordTrace_append hprefix tailTrace_2109453
  have hstable : (prefixWord ++ tailWord_2109453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109453).length < 2 ^ (prefixWord ++ tailWord_2109453).sum := by decide
  have hdescent : baseEnd_2109453 < baseStart_2109453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109459 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 1, 2, 2]
def baseStart_2109459 : Nat := 118140960795 + 2109459 * 2 ^ 59
def prefixEnd_2109459 : Nat := 4983230072969 + 3 ^ 40 * 2109459 * 2
def baseEnd_2109459 : Nat := 1083166387952767465661281

theorem tailTrace_2109459 : CollatzResearch.WordTrace tailWord_2109459 prefixEnd_2109459 1083166387952767465661281 := by
  unfold tailWord_2109459
  simp only [CollatzResearch.WordTrace]
  refine ⟨76938290464797784759995431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51292193643198523173330287 76938290464797784759995431)
  ·
    refine ⟨115407435697196677139993147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76938290464797784759995431 115407435697196677139993147)
    ·
      refine ⟨173111153545795015709989721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115407435697196677139993147 173111153545795015709989721)
      ·
        refine ⟨129833365159346261782492291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173111153545795015709989721 129833365159346261782492291)
        ·
          refine ⟨194750047739019392673738437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129833365159346261782492291 194750047739019392673738437)
          ·
            refine ⟨36515633951066136126325957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194750047739019392673738437 36515633951066136126325957)
            ·
              refine ⟨6846681365824900523686117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36515633951066136126325957 6846681365824900523686117)
              ·
                refine ⟨1283752756092168848191147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6846681365824900523686117 1283752756092168848191147)
                ·
                  refine ⟨1925629134138253272286721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283752756092168848191147 1925629134138253272286721)
                  ·
                    refine ⟨1444221850603689954215041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1925629134138253272286721 1444221850603689954215041)
                    ·
                      refine ⟨1083166387952767465661281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444221850603689954215041 1083166387952767465661281)
                      ·
                        rfl

theorem cell23_2109459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 2, 2].length) (baseStart_2109459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109459 prefixEnd_2109459 := by exact prefixLift 2109459
  have htrace : WordTrace (prefixWord ++ tailWord_2109459) baseStart_2109459 baseEnd_2109459 := by
    simpa [prefixWord, tailWord_2109459, baseEnd_2109459] using wordTrace_append hprefix tailTrace_2109459
  have hstable : (prefixWord ++ tailWord_2109459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109459).length < 2 ^ (prefixWord ++ tailWord_2109459).sum := by decide
  have hdescent : baseEnd_2109459 < baseStart_2109459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109469 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2109469 : Nat := 118140960795 + 2109469 * 2 ^ 59
def prefixEnd_2109469 : Nat := 4983230072969 + 3 ^ 40 * 2109469 * 2
def baseEnd_2109469 : Nat := 361057174253104142178745

theorem tailTrace_2109469 : CollatzResearch.WordTrace tailWord_2109469 prefixEnd_2109469 361057174253104142178745 := by
  unfold tailWord_2109469
  simp only [CollatzResearch.WordTrace]
  refine ⟨76938655194761556467859461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51292436796507704311906307 76938655194761556467859461)
  ·
    refine ⟨14425997849017791837723649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76938655194761556467859461 14425997849017791837723649)
    ·
      refine ⟨10819498386763343878292737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14425997849017791837723649 10819498386763343878292737)
      ·
        refine ⟨8114623790072507908719553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10819498386763343878292737 8114623790072507908719553)
        ·
          refine ⟨6085967842554380931539665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8114623790072507908719553 6085967842554380931539665)
          ·
            refine ⟨4564475881915785698654749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6085967842554380931539665 4564475881915785698654749)
            ·
              refine ⟨1711678455718419636995531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4564475881915785698654749 1711678455718419636995531)
              ·
                refine ⟨2567517683577629455493297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711678455718419636995531 2567517683577629455493297)
                ·
                  refine ⟨1925638262683222091619973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567517683577629455493297 1925638262683222091619973)
                  ·
                    refine ⟨361057174253104142178745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925638262683222091619973 361057174253104142178745)
                    ·
                      rfl

theorem cell23_2109469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2109469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109469 prefixEnd_2109469 := by exact prefixLift 2109469
  have htrace : WordTrace (prefixWord ++ tailWord_2109469) baseStart_2109469 baseEnd_2109469 := by
    simpa [prefixWord, tailWord_2109469, baseEnd_2109469] using wordTrace_append hprefix tailTrace_2109469
  have hstable : (prefixWord ++ tailWord_2109469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109469).length < 2 ^ (prefixWord ++ tailWord_2109469).sum := by decide
  have hdescent : baseEnd_2109469 < baseStart_2109469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109482 : List Nat := [3, 1, 4, 1, 2, 3, 2, 7]
def baseStart_2109482 : Nat := 118140960795 + 2109482 * 2 ^ 59
def prefixEnd_2109482 : Nat := 4983230072969 + 3 ^ 40 * 2109482 * 2
def baseEnd_2109482 : Nat := 40117711037326699099025

theorem tailTrace_2109482 : CollatzResearch.WordTrace tailWord_2109482 prefixEnd_2109482 40117711037326699099025 := by
  unfold tailWord_2109482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19234782335928614922020675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51292752895809639792055133 19234782335928614922020675)
  ·
    refine ⟨28852173503892922383031013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19234782335928614922020675 28852173503892922383031013)
    ·
      refine ⟨5409782531979922946818315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28852173503892922383031013 5409782531979922946818315)
      ·
        refine ⟨8114673797969884420227473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5409782531979922946818315 8114673797969884420227473)
        ·
          refine ⟨6086005348477413315170605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8114673797969884420227473 6086005348477413315170605)
          ·
            refine ⟨2282252005679029993188977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6086005348477413315170605 2282252005679029993188977)
            ·
              refine ⟨1711689004259272494891733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282252005679029993188977 1711689004259272494891733)
              ·
                refine ⟨40117711037326699099025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1711689004259272494891733 40117711037326699099025)
                ·
                  rfl

theorem cell23_2109482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_2109482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109482 prefixEnd_2109482 := by exact prefixLift 2109482
  have htrace : WordTrace (prefixWord ++ tailWord_2109482) baseStart_2109482 baseEnd_2109482 := by
    simpa [prefixWord, tailWord_2109482, baseEnd_2109482] using wordTrace_append hprefix tailTrace_2109482
  have hstable : (prefixWord ++ tailWord_2109482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109482).length < 2 ^ (prefixWord ++ tailWord_2109482).sum := by decide
  have hdescent : baseEnd_2109482 < baseStart_2109482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109488 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_2109488 : Nat := 118140960795 + 2109488 * 2 ^ 59
def prefixEnd_2109488 : Nat := 4983230072969 + 3 ^ 40 * 2109488 * 2
def baseEnd_2109488 : Nat := 1083181278891747852198647

theorem tailTrace_2109488 : CollatzResearch.WordTrace tailWord_2109488 prefixEnd_2109488 1083181278891747852198647 := by
  unfold tailWord_2109488
  simp only [CollatzResearch.WordTrace]
  refine ⟨38469674090846361356400559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51292898787795148475200745 38469674090846361356400559)
  ·
    refine ⟨57704511136269542034600839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38469674090846361356400559 57704511136269542034600839)
    ·
      refine ⟨86556766704404313051901259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57704511136269542034600839 86556766704404313051901259)
      ·
        refine ⟨129835150056606469577851889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86556766704404313051901259 129835150056606469577851889)
        ·
          refine ⟨97376362542454852183388917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129835150056606469577851889 97376362542454852183388917)
          ·
            refine ⟨9129033988355142392192711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97376362542454852183388917 9129033988355142392192711)
            ·
              refine ⟨13693550982532713588289067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9129033988355142392192711 13693550982532713588289067)
              ·
                refine ⟨20540326473799070382433601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13693550982532713588289067 20540326473799070382433601)
                ·
                  refine ⟨15405244855349302786825201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20540326473799070382433601 15405244855349302786825201)
                  ·
                    refine ⟨11553933641511977090118901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15405244855349302786825201 11553933641511977090118901)
                    ·
                      refine ⟨1083181278891747852198647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11553933641511977090118901 1083181278891747852198647)
                      ·
                        rfl

theorem cell23_2109488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_2109488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109488 prefixEnd_2109488 := by exact prefixLift 2109488
  have htrace : WordTrace (prefixWord ++ tailWord_2109488) baseStart_2109488 baseEnd_2109488 := by
    simpa [prefixWord, tailWord_2109488, baseEnd_2109488] using wordTrace_append hprefix tailTrace_2109488
  have hstable : (prefixWord ++ tailWord_2109488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109488).length < 2 ^ (prefixWord ++ tailWord_2109488).sum := by decide
  have hdescent : baseEnd_2109488 < baseStart_2109488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109498 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_2109498 : Nat := 118140960795 + 2109498 * 2 ^ 59
def prefixEnd_2109498 : Nat := 4983230072969 + 3 ^ 40 * 2109498 * 2
def baseEnd_2109498 : Nat := 1083186413698292813073601

theorem tailTrace_2109498 : CollatzResearch.WordTrace tailWord_2109498 prefixEnd_2109498 1083186413698292813073601 := by
  unfold tailWord_2109498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19234928227914123605166287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51293141941104329613776765 19234928227914123605166287)
  ·
    refine ⟨28852392341871185407749431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19234928227914123605166287 28852392341871185407749431)
    ·
      refine ⟨43278588512806778111624147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28852392341871185407749431 43278588512806778111624147)
      ·
        refine ⟨64917882769210167167436221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43278588512806778111624147 64917882769210167167436221)
        ·
          refine ⟨24344206038453812687788583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64917882769210167167436221 24344206038453812687788583)
          ·
            refine ⟨36516309057680719031682875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24344206038453812687788583 36516309057680719031682875)
            ·
              refine ⟨54774463586521078547524313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36516309057680719031682875 54774463586521078547524313)
              ·
                refine ⟨41080847689890808910643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54774463586521078547524313 41080847689890808910643235)
                ·
                  refine ⟨61621271534836213365964853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41080847689890808910643235 61621271534836213365964853)
                  ·
                    refine ⟨5776994206390895003059205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61621271534836213365964853 5776994206390895003059205)
                    ·
                      refine ⟨1083186413698292813073601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5776994206390895003059205 1083186413698292813073601)
                      ·
                        rfl

theorem cell23_2109498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_2109498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109498 prefixEnd_2109498 := by exact prefixLift 2109498
  have htrace : WordTrace (prefixWord ++ tailWord_2109498) baseStart_2109498 baseEnd_2109498 := by
    simpa [prefixWord, tailWord_2109498, baseEnd_2109498] using wordTrace_append hprefix tailTrace_2109498
  have hstable : (prefixWord ++ tailWord_2109498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109498).length < 2 ^ (prefixWord ++ tailWord_2109498).sum := by decide
  have hdescent : baseEnd_2109498 < baseStart_2109498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109510 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2109510 : Nat := 118140960795 + 2109510 * 2 ^ 59
def prefixEnd_2109510 : Nat := 4983230072969 + 3 ^ 40 * 2109510 * 2
def baseEnd_2109510 : Nat := 1083192575466146766123547

theorem tailTrace_2109510 : CollatzResearch.WordTrace tailWord_2109510 prefixEnd_2109510 1083192575466146766123547 := by
  unfold tailWord_2109510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404379705862906889690687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51293433725075346980067989 2404379705862906889690687)
  ·
    refine ⟨3606569558794360334536031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2404379705862906889690687 3606569558794360334536031)
    ·
      refine ⟨5409854338191540501804047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3606569558794360334536031 5409854338191540501804047)
      ·
        refine ⟨8114781507287310752706071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5409854338191540501804047 8114781507287310752706071)
        ·
          refine ⟨12172172260930966129059107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8114781507287310752706071 12172172260930966129059107)
          ·
            refine ⟨18258258391396449193588661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12172172260930966129059107 18258258391396449193588661)
            ·
              refine ⟨1711711724193417111898937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18258258391396449193588661 1711711724193417111898937)
              ·
                refine ⟨1283783793145062833924203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711711724193417111898937 1283783793145062833924203)
                ·
                  refine ⟨1925675689717594250886305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283783793145062833924203 1925675689717594250886305)
                  ·
                    refine ⟨1444256767288195688164729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1925675689717594250886305 1444256767288195688164729)
                    ·
                      refine ⟨1083192575466146766123547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444256767288195688164729 1083192575466146766123547)
                      ·
                        rfl

theorem cell23_2109510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2109510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109510 prefixEnd_2109510 := by exact prefixLift 2109510
  have htrace : WordTrace (prefixWord ++ tailWord_2109510) baseStart_2109510 baseEnd_2109510 := by
    simpa [prefixWord, tailWord_2109510, baseEnd_2109510] using wordTrace_append hprefix tailTrace_2109510
  have hstable : (prefixWord ++ tailWord_2109510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109510).length < 2 ^ (prefixWord ++ tailWord_2109510).sum := by decide
  have hdescent : baseEnd_2109510 < baseStart_2109510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109515 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 3, 4, 2]
def baseStart_2109515 : Nat := 118140960795 + 2109515 * 2 ^ 59
def prefixEnd_2109515 : Nat := 4983230072969 + 3 ^ 40 * 2109515 * 2
def baseEnd_2109515 : Nat := 1083195142869419246561023

theorem tailTrace_2109515 : CollatzResearch.WordTrace tailWord_2109515 prefixEnd_2109515 1083195142869419246561023 := by
  unfold tailWord_2109515
  simp only [CollatzResearch.WordTrace]
  refine ⟨76940332952594906324033999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51293555301729937549355999 76940332952594906324033999)
  ·
    refine ⟨115410499428892359486050999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76940332952594906324033999 115410499428892359486050999)
    ·
      refine ⟨173115749143338539229076499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115410499428892359486050999 173115749143338539229076499)
      ·
        refine ⟨259673623715007808843614749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173115749143338539229076499 259673623715007808843614749)
        ·
          refine ⟨97377608893127928316355531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259673623715007808843614749 97377608893127928316355531)
          ·
            refine ⟨146066413339691892474533297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97377608893127928316355531 146066413339691892474533297)
            ·
              refine ⟨109549810004768919355899973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146066413339691892474533297 109549810004768919355899973)
              ·
                refine ⟨20540589375894172379231245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109549810004768919355899973 20540589375894172379231245)
                ·
                  refine ⟨7702721015960314642211717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20540589375894172379231245 7702721015960314642211717)
                  ·
                    refine ⟨1444260190492558995414697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7702721015960314642211717 1444260190492558995414697)
                    ·
                      refine ⟨1083195142869419246561023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444260190492558995414697 1083195142869419246561023)
                      ·
                        rfl

theorem cell23_2109515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4, 2].length) (baseStart_2109515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109515 prefixEnd_2109515 := by exact prefixLift 2109515
  have htrace : WordTrace (prefixWord ++ tailWord_2109515) baseStart_2109515 baseEnd_2109515 := by
    simpa [prefixWord, tailWord_2109515, baseEnd_2109515] using wordTrace_append hprefix tailTrace_2109515
  have hstable : (prefixWord ++ tailWord_2109515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109515).length < 2 ^ (prefixWord ++ tailWord_2109515).sum := by decide
  have hdescent : baseEnd_2109515 < baseStart_2109515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109568 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_2109568 : Nat := 118140960795 + 2109568 * 2 ^ 59
def prefixEnd_2109568 : Nat := 4983230072969 + 3 ^ 40 * 2109568 * 2
def baseEnd_2109568 : Nat := 361074119114702513066093

theorem tailTrace_2109568 : CollatzResearch.WordTrace tailWord_2109568 prefixEnd_2109568 361074119114702513066093 := by
  unfold tailWord_2109568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38471133010701448187856679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51294844014268597583808905 38471133010701448187856679)
  ·
    refine ⟨57706699516052172281785019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38471133010701448187856679 57706699516052172281785019)
    ·
      refine ⟨86560049274078258422677529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57706699516052172281785019 86560049274078258422677529)
      ·
        refine ⟨64920036955558693817008147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86560049274078258422677529 64920036955558693817008147)
        ·
          refine ⟨97380055433338040725512221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64920036955558693817008147 97380055433338040725512221)
          ·
            refine ⟨36517520787501765272067083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97380055433338040725512221 36517520787501765272067083)
            ·
              refine ⟨54776281181252647908100625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36517520787501765272067083 54776281181252647908100625)
              ·
                refine ⟨41082210885939485931075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54776281181252647908100625 41082210885939485931075469)
                ·
                  refine ⟨15405829082227307224153301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41082210885939485931075469 15405829082227307224153301)
                  ·
                    refine ⟨361074119114702513066093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15405829082227307224153301 361074119114702513066093)
                    ·
                      rfl

theorem cell23_2109568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_2109568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109568 prefixEnd_2109568 := by exact prefixLift 2109568
  have htrace : WordTrace (prefixWord ++ tailWord_2109568) baseStart_2109568 baseEnd_2109568 := by
    simpa [prefixWord, tailWord_2109568, baseEnd_2109568] using wordTrace_append hprefix tailTrace_2109568
  have hstable : (prefixWord ++ tailWord_2109568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109568).length < 2 ^ (prefixWord ++ tailWord_2109568).sum := by decide
  have hdescent : baseEnd_2109568 < baseStart_2109568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109572 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 5]
def baseStart_2109572 : Nat := 118140960795 + 2109572 * 2 ^ 59
def prefixEnd_2109572 : Nat := 4983230072969 + 3 ^ 40 * 2109572 * 2
def baseEnd_2109572 : Nat := 120358267918525058172029

theorem tailTrace_2109572 : CollatzResearch.WordTrace tailWord_2109572 prefixEnd_2109572 120358267918525058172029 := by
  unfold tailWord_2109572
  simp only [CollatzResearch.WordTrace]
  refine ⟨38471205956694202529429485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51294941275592270039239313 38471205956694202529429485)
  ·
    refine ⟨14426702233760325948536057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38471205956694202529429485 14426702233760325948536057)
    ·
      refine ⟨10820026675320244461402043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14426702233760325948536057 10820026675320244461402043)
      ·
        refine ⟨16230040012980366692103065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10820026675320244461402043 16230040012980366692103065)
        ·
          refine ⟨12172530009735275019077299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16230040012980366692103065 12172530009735275019077299)
          ·
            refine ⟨18258795014602912528615949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12172530009735275019077299 18258795014602912528615949)
            ·
              refine ⟨6847048130476092198230981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18258795014602912528615949 6847048130476092198230981)
              ·
                refine ⟨1283821524464267287168309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6847048130476092198230981 1283821524464267287168309)
                ·
                  refine ⟨120358267918525058172029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283821524464267287168309 120358267918525058172029)
                  ·
                    rfl

theorem cell23_2109572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_2109572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109572 prefixEnd_2109572 := by exact prefixLift 2109572
  have htrace : WordTrace (prefixWord ++ tailWord_2109572) baseStart_2109572 baseEnd_2109572 := by
    simpa [prefixWord, tailWord_2109572, baseEnd_2109572] using wordTrace_append hprefix tailTrace_2109572
  have hstable : (prefixWord ++ tailWord_2109572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109572).length < 2 ^ (prefixWord ++ tailWord_2109572).sum := by decide
  have hdescent : baseEnd_2109572 < baseStart_2109572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109602 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2109602 : Nat := 118140960795 + 2109602 * 2 ^ 59
def prefixEnd_2109602 : Nat := 4983230072969 + 3 ^ 40 * 2109602 * 2
def baseEnd_2109602 : Nat := 361079938562120135391041

theorem tailTrace_2109602 : CollatzResearch.WordTrace tailWord_2109602 prefixEnd_2109602 361079938562120135391041 := by
  unfold tailWord_2109602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235876525819930045612765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51295670735519813454967373 19235876525819930045612765)
  ·
    refine ⟨7213453697182473767104787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19235876525819930045612765 7213453697182473767104787)
    ·
      refine ⟨10820180545773710650657181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7213453697182473767104787 10820180545773710650657181)
      ·
        refine ⟨4057567704665141493996443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10820180545773710650657181 4057567704665141493996443)
        ·
          refine ⟨6086351556997712240994665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057567704665141493996443 6086351556997712240994665)
          ·
            refine ⟨4564763667748284180745999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6086351556997712240994665 4564763667748284180745999)
            ·
              refine ⟨6847145501622426271118999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4564763667748284180745999 6847145501622426271118999)
              ·
                refine ⟨10270718252433639406678499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6847145501622426271118999 10270718252433639406678499)
                ·
                  refine ⟨15406077378650459110017749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10270718252433639406678499 15406077378650459110017749)
                  ·
                    refine ⟨361079938562120135391041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15406077378650459110017749 361079938562120135391041)
                    ·
                      rfl

theorem cell23_2109602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2109602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109602 prefixEnd_2109602 := by exact prefixLift 2109602
  have htrace : WordTrace (prefixWord ++ tailWord_2109602) baseStart_2109602 baseEnd_2109602 := by
    simpa [prefixWord, tailWord_2109602, baseEnd_2109602] using wordTrace_append hprefix tailTrace_2109602
  have hstable : (prefixWord ++ tailWord_2109602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109602).length < 2 ^ (prefixWord ++ tailWord_2109602).sum := by decide
  have hdescent : baseEnd_2109602 < baseStart_2109602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109605 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_2109605 : Nat := 118140960795 + 2109605 * 2 ^ 59
def prefixEnd_2109605 : Nat := 4983230072969 + 3 ^ 40 * 2109605 * 2
def baseEnd_2109605 : Nat := 1083241356128323894435609

theorem tailTrace_2109605 : CollatzResearch.WordTrace tailWord_2109605 prefixEnd_2109605 1083241356128323894435609 := by
  unfold tailWord_2109605
  simp only [CollatzResearch.WordTrace]
  refine ⟨76943615522268851694810269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51295743681512567796540179 76943615522268851694810269)
  ·
    refine ⟨28853855820850819385553851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76943615522268851694810269 28853855820850819385553851)
    ·
      refine ⟨43280783731276229078330777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28853855820850819385553851 43280783731276229078330777)
      ·
        refine ⟨32460587798457171808748083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43280783731276229078330777 32460587798457171808748083)
        ·
          refine ⟨48690881697685757713122125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32460587798457171808748083 48690881697685757713122125)
          ·
            refine ⟨18259080636632159142420797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48690881697685757713122125 18259080636632159142420797)
            ·
              refine ⟨6847155238737059678407799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18259080636632159142420797 6847155238737059678407799)
              ·
                refine ⟨10270732858105589517611699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6847155238737059678407799 10270732858105589517611699)
                ·
                  refine ⟨15406099287158384276417549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10270732858105589517611699 15406099287158384276417549)
                  ·
                    refine ⟨5777287232684394103656581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15406099287158384276417549 5777287232684394103656581)
                    ·
                      refine ⟨1083241356128323894435609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5777287232684394103656581 1083241356128323894435609)
                      ·
                        rfl

theorem cell23_2109605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_2109605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109605 prefixEnd_2109605 := by exact prefixLift 2109605
  have htrace : WordTrace (prefixWord ++ tailWord_2109605) baseStart_2109605 baseEnd_2109605 := by
    simpa [prefixWord, tailWord_2109605, baseEnd_2109605] using wordTrace_append hprefix tailTrace_2109605
  have hstable : (prefixWord ++ tailWord_2109605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109605).length < 2 ^ (prefixWord ++ tailWord_2109605).sum := by decide
  have hdescent : baseEnd_2109605 < baseStart_2109605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109615 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 7, 4]
def baseStart_2109615 : Nat := 118140960795 + 2109615 * 2 ^ 59
def prefixEnd_2109615 : Nat := 4983230072969 + 3 ^ 40 * 2109615 * 2
def baseEnd_2109615 : Nat := 361082163644956285103521

theorem tailTrace_2109615 : CollatzResearch.WordTrace tailWord_2109615 prefixEnd_2109615 361082163644956285103521 := by
  unfold tailWord_2109615
  simp only [CollatzResearch.WordTrace]
  refine ⟨76943980252232623402674299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51295986834821748935116199 76943980252232623402674299)
  ·
    refine ⟨115415970378348935104011449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76943980252232623402674299 115415970378348935104011449)
    ·
      refine ⟨86561977783761701328008587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115415970378348935104011449 86561977783761701328008587)
      ·
        refine ⟨129842966675642551992012881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86561977783761701328008587 129842966675642551992012881)
        ·
          refine ⟨97382225006731913994009661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129842966675642551992012881 97382225006731913994009661)
          ·
            refine ⟨36518334377524467747753623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97382225006731913994009661 36518334377524467747753623)
            ·
              refine ⟨54777501566286701621630435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36518334377524467747753623 54777501566286701621630435)
              ·
                refine ⟨82166252349430052432445653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54777501566286701621630435 82166252349430052432445653)
                ·
                  refine ⟨1925771539439766853885445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82166252349430052432445653 1925771539439766853885445)
                  ·
                    refine ⟨361082163644956285103521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925771539439766853885445 361082163644956285103521)
                    ·
                      rfl

theorem cell23_2109615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_2109615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109615 prefixEnd_2109615 := by exact prefixLift 2109615
  have htrace : WordTrace (prefixWord ++ tailWord_2109615) baseStart_2109615 baseEnd_2109615 := by
    simpa [prefixWord, tailWord_2109615, baseEnd_2109615] using wordTrace_append hprefix tailTrace_2109615
  have hstable : (prefixWord ++ tailWord_2109615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109615).length < 2 ^ (prefixWord ++ tailWord_2109615).sum := by decide
  have hdescent : baseEnd_2109615 < baseStart_2109615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109632 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_2109632 : Nat := 118140960795 + 2109632 * 2 ^ 59
def prefixEnd_2109632 : Nat := 4983230072969 + 3 ^ 40 * 2109632 * 2
def baseEnd_2109632 : Nat := 361085073368665096265995

theorem tailTrace_2109632 : CollatzResearch.WordTrace tailWord_2109632 prefixEnd_2109632 361085073368665096265995 := by
  unfold tailWord_2109632
  simp only [CollatzResearch.WordTrace]
  refine ⟨38472300146585517653021575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51296400195447356870695433 38472300146585517653021575)
  ·
    refine ⟨57708450219878276479532363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38472300146585517653021575 57708450219878276479532363)
    ·
      refine ⟨86562675329817414719298545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57708450219878276479532363 86562675329817414719298545)
      ·
        refine ⟨64922006497363061039473909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86562675329817414719298545 64922006497363061039473909)
        ·
          refine ⟨6086438109127786972450679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64922006497363061039473909 6086438109127786972450679)
          ·
            refine ⟨9129657163691680458676019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6086438109127786972450679 9129657163691680458676019)
            ·
              refine ⟨13694485745537520688014029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9129657163691680458676019 13694485745537520688014029)
              ·
                refine ⟨5135432154576570258005261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13694485745537520688014029 5135432154576570258005261)
                ·
                  refine ⟨1925787057966213846751973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5135432154576570258005261 1925787057966213846751973)
                  ·
                    refine ⟨361085073368665096265995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925787057966213846751973 361085073368665096265995)
                    ·
                      rfl

theorem cell23_2109632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_2109632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109632 prefixEnd_2109632 := by exact prefixLift 2109632
  have htrace : WordTrace (prefixWord ++ tailWord_2109632) baseStart_2109632 baseEnd_2109632 := by
    simpa [prefixWord, tailWord_2109632, baseEnd_2109632] using wordTrace_append hprefix tailTrace_2109632
  have hstable : (prefixWord ++ tailWord_2109632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109632).length < 2 ^ (prefixWord ++ tailWord_2109632).sum := by decide
  have hdescent : baseEnd_2109632 < baseStart_2109632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109655 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_2109655 : Nat := 118140960795 + 2109655 * 2 ^ 59
def prefixEnd_2109655 : Nat := 4983230072969 + 3 ^ 40 * 2109655 * 2
def baseEnd_2109655 : Nat := 1083267030161048698810379

theorem tailTrace_2109655 : CollatzResearch.WordTrace tailWord_2109655 prefixEnd_2109655 1083267030161048698810379 := by
  unfold tailWord_2109655
  simp only [CollatzResearch.WordTrace]
  refine ⟨76945439172087710234130419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51296959448058473489420279 76945439172087710234130419)
  ·
    refine ⟨115418158758131565351195629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76945439172087710234130419 115418158758131565351195629)
    ·
      refine ⟨43281809534299337006698361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115418158758131565351195629 43281809534299337006698361)
      ·
        refine ⟨32461357150724502755023771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43281809534299337006698361 32461357150724502755023771)
        ·
          refine ⟨48692035726086754132535657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32461357150724502755023771 48692035726086754132535657)
          ·
            refine ⟨36519026794565065599401743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48692035726086754132535657 36519026794565065599401743)
            ·
              refine ⟨54778540191847598399102615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36519026794565065599401743 54778540191847598399102615)
              ·
                refine ⟨82167810287771397598653923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54778540191847598399102615 82167810287771397598653923)
                ·
                  refine ⟨123251715431657096397980885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82167810287771397598653923 123251715431657096397980885)
                  ·
                    refine ⟨2888712080429463196827677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 123251715431657096397980885 2888712080429463196827677)
                    ·
                      refine ⟨1083267030161048698810379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2888712080429463196827677 1083267030161048698810379)
                      ·
                        rfl

theorem cell23_2109655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_2109655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109655 prefixEnd_2109655 := by exact prefixLift 2109655
  have htrace : WordTrace (prefixWord ++ tailWord_2109655) baseStart_2109655 baseEnd_2109655 := by
    simpa [prefixWord, tailWord_2109655, baseEnd_2109655] using wordTrace_append hprefix tailTrace_2109655
  have hstable : (prefixWord ++ tailWord_2109655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109655).length < 2 ^ (prefixWord ++ tailWord_2109655).sum := by decide
  have hdescent : baseEnd_2109655 < baseStart_2109655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109715 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_2109715 : Nat := 118140960795 + 2109715 * 2 ^ 59
def prefixEnd_2109715 : Nat := 4983230072969 + 3 ^ 40 * 2109715 * 2
def baseEnd_2109715 : Nat := 1083297839000318464060103

theorem tailTrace_2109715 : CollatzResearch.WordTrace tailWord_2109715 prefixEnd_2109715 1083297839000318464060103 := by
  unfold tailWord_2109715
  simp only [CollatzResearch.WordTrace]
  refine ⟨76947627551870340481314599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51298418367913560320876399 76947627551870340481314599)
  ·
    refine ⟨115421441327805510721971899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76947627551870340481314599 115421441327805510721971899)
    ·
      refine ⟨173132161991708266082957849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115421441327805510721971899 173132161991708266082957849)
      ·
        refine ⟨129849121493781199562218387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173132161991708266082957849 129849121493781199562218387)
        ·
          refine ⟨194773682240671799343327581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129849121493781199562218387 194773682240671799343327581)
          ·
            refine ⟨73040130840251924753747843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194773682240671799343327581 73040130840251924753747843)
            ·
              refine ⟨109560196260377887130621765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73040130840251924753747843 109560196260377887130621765)
              ·
                refine ⟨20542536798820853836991581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109560196260377887130621765 20542536798820853836991581)
                ·
                  refine ⟨7703451299557820188871843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20542536798820853836991581 7703451299557820188871843)
                  ·
                    refine ⟨11555176949336730283307765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7703451299557820188871843 11555176949336730283307765)
                    ·
                      refine ⟨1083297839000318464060103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11555176949336730283307765 1083297839000318464060103)
                      ·
                        rfl

theorem cell23_2109715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_2109715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109715 prefixEnd_2109715 := by exact prefixLift 2109715
  have htrace : WordTrace (prefixWord ++ tailWord_2109715) baseStart_2109715 baseEnd_2109715 := by
    simpa [prefixWord, tailWord_2109715, baseEnd_2109715] using wordTrace_append hprefix tailTrace_2109715
  have hstable : (prefixWord ++ tailWord_2109715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109715).length < 2 ^ (prefixWord ++ tailWord_2109715).sum := by decide
  have hdescent : baseEnd_2109715 < baseStart_2109715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109780 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_2109780 : Nat := 118140960795 + 2109780 * 2 ^ 59
def prefixEnd_2109780 : Nat := 4983230072969 + 3 ^ 40 * 2109780 * 2
def baseEnd_2109780 : Nat := 1083331215242860709747305

theorem tailTrace_2109780 : CollatzResearch.WordTrace tailWord_2109780 prefixEnd_2109780 1083331215242860709747305 := by
  unfold tailWord_2109780
  simp only [CollatzResearch.WordTrace]
  refine ⟨38474999148317428291215397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51299998864423237721620529 38474999148317428291215397)
  ·
    refine ⟨7214062340309517804602887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38474999148317428291215397 7214062340309517804602887)
    ·
      refine ⟨10821093510464276706904331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214062340309517804602887 10821093510464276706904331)
      ·
        refine ⟨16231640265696415060356497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10821093510464276706904331 16231640265696415060356497)
        ·
          refine ⟨12173730199272311295267373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16231640265696415060356497 12173730199272311295267373)
          ·
            refine ⟨4565148824727116735725265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12173730199272311295267373 4565148824727116735725265)
            ·
              refine ⟨3423861618545337551793949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4565148824727116735725265 3423861618545337551793949)
              ·
                refine ⟨1283948106954501581922731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423861618545337551793949 1283948106954501581922731)
                ·
                  refine ⟨1925922160431752372884097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283948106954501581922731 1925922160431752372884097)
                  ·
                    refine ⟨1444441620323814279663073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1925922160431752372884097 1444441620323814279663073)
                    ·
                      refine ⟨1083331215242860709747305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444441620323814279663073 1083331215242860709747305)
                      ·
                        rfl

theorem cell23_2109780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_2109780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109780 prefixEnd_2109780 := by exact prefixLift 2109780
  have htrace : WordTrace (prefixWord ++ tailWord_2109780) baseStart_2109780 baseEnd_2109780 := by
    simpa [prefixWord, tailWord_2109780, baseEnd_2109780] using wordTrace_append hprefix tailTrace_2109780
  have hstable : (prefixWord ++ tailWord_2109780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109780).length < 2 ^ (prefixWord ++ tailWord_2109780).sum := by decide
  have hdescent : baseEnd_2109780 < baseStart_2109780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109836 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_2109836 : Nat := 118140960795 + 2109836 * 2 ^ 59
def prefixEnd_2109836 : Nat := 4983230072969 + 3 ^ 40 * 2109836 * 2
def baseEnd_2109836 : Nat := 1083359970159512490647047

theorem tailTrace_2109836 : CollatzResearch.WordTrace tailWord_2109836 prefixEnd_2109836 1083359970159512490647047 := by
  unfold tailWord_2109836
  simp only [CollatzResearch.WordTrace]
  refine ⟨38476020392215989073234681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51301360522954652097646241 38476020392215989073234681)
  ·
    refine ⟨28857015294161991804926011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38476020392215989073234681 28857015294161991804926011)
    ·
      refine ⟨43285522941242987707389017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28857015294161991804926011 43285522941242987707389017)
      ·
        refine ⟨32464142205932240780541763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43285522941242987707389017 32464142205932240780541763)
        ·
          refine ⟨48696213308898361170812645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32464142205932240780541763 48696213308898361170812645)
          ·
            refine ⟨9130539995418442719527371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48696213308898361170812645 9130539995418442719527371)
            ·
              refine ⟨13695809993127664079291057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9130539995418442719527371 13695809993127664079291057)
              ·
                refine ⟨10271857494845748059468293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13695809993127664079291057 10271857494845748059468293)
                ·
                  refine ⟨1925973280283577761150305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10271857494845748059468293 1925973280283577761150305)
                  ·
                    refine ⟨1444479960212683320862729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1925973280283577761150305 1444479960212683320862729)
                    ·
                      refine ⟨1083359970159512490647047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444479960212683320862729 1083359970159512490647047)
                      ·
                        rfl

theorem cell23_2109836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_2109836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109836 prefixEnd_2109836 := by exact prefixLift 2109836
  have htrace : WordTrace (prefixWord ++ tailWord_2109836) baseStart_2109836 baseEnd_2109836 := by
    simpa [prefixWord, tailWord_2109836, baseEnd_2109836] using wordTrace_append hprefix tailTrace_2109836
  have hstable : (prefixWord ++ tailWord_2109836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109836).length < 2 ^ (prefixWord ++ tailWord_2109836).sum := by decide
  have hdescent : baseEnd_2109836 < baseStart_2109836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109859 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 7]
def baseStart_2109859 : Nat := 118140960795 + 2109859 * 2 ^ 59
def prefixEnd_2109859 : Nat := 4983230072969 + 3 ^ 40 * 2109859 * 2
def baseEnd_2109859 : Nat := 120374642246062877851049

theorem tailTrace_2109859 : CollatzResearch.WordTrace tailWord_2109859 prefixEnd_2109859 120374642246062877851049 := by
  unfold tailWord_2109859
  simp only [CollatzResearch.WordTrace]
  refine ⟨76952879663348653074556631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51301919775565768716371087 76952879663348653074556631)
  ·
    refine ⟨115429319495022979611834947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76952879663348653074556631 115429319495022979611834947)
    ·
      refine ⟨173143979242534469417752421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115429319495022979611834947 173143979242534469417752421)
      ·
        refine ⟨32464496107975213015828579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173143979242534469417752421 32464496107975213015828579)
        ·
          refine ⟨48696744161962819523742869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32464496107975213015828579 48696744161962819523742869)
          ·
            refine ⟨2282659882592007165175447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48696744161962819523742869 2282659882592007165175447)
            ·
              refine ⟨3423989823888010747763171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282659882592007165175447 3423989823888010747763171)
              ·
                refine ⟨5135984735832016121644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423989823888010747763171 5135984735832016121644757)
                ·
                  refine ⟨120374642246062877851049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5135984735832016121644757 120374642246062877851049)
                  ·
                    rfl

theorem cell23_2109859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 7].length) (baseStart_2109859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109859 prefixEnd_2109859 := by exact prefixLift 2109859
  have htrace : WordTrace (prefixWord ++ tailWord_2109859) baseStart_2109859 baseEnd_2109859 := by
    simpa [prefixWord, tailWord_2109859, baseEnd_2109859] using wordTrace_append hprefix tailTrace_2109859
  have hstable : (prefixWord ++ tailWord_2109859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109859).length < 2 ^ (prefixWord ++ tailWord_2109859).sum := by decide
  have hdescent : baseEnd_2109859 < baseStart_2109859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109912 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2109912 : Nat := 118140960795 + 2109912 * 2 ^ 59
def prefixEnd_2109912 : Nat := 4983230072969 + 3 ^ 40 * 2109912 * 2
def baseEnd_2109912 : Nat := 1083398994689254193296697

theorem tailTrace_2109912 : CollatzResearch.WordTrace tailWord_2109912 prefixEnd_2109912 1083398994689254193296697 := by
  unfold tailWord_2109912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38477406366078321563117995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51303208488104428750823993 38477406366078321563117995)
  ·
    refine ⟨57716109549117482344676993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38477406366078321563117995 57716109549117482344676993)
    ·
      refine ⟨43287082161838111758507745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57716109549117482344676993 43287082161838111758507745)
      ·
        refine ⟨32465311621378583818880809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43287082161838111758507745 32465311621378583818880809)
        ·
          refine ⟨24348983716033937864160607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32465311621378583818880809 24348983716033937864160607)
          ·
            refine ⟨36523475574050906796240911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24348983716033937864160607 36523475574050906796240911)
            ·
              refine ⟨54785213361076360194361367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36523475574050906796240911 54785213361076360194361367)
              ·
                refine ⟨82177820041614540291542051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54785213361076360194361367 82177820041614540291542051)
                ·
                  refine ⟨123266730062421810437313077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82177820041614540291542051 123266730062421810437313077)
                  ·
                    refine ⟨11556255943352044728498101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123266730062421810437313077 11556255943352044728498101)
                    ·
                      refine ⟨1083398994689254193296697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11556255943352044728498101 1083398994689254193296697)
                      ·
                        rfl

theorem cell23_2109912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2109912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109912 prefixEnd_2109912 := by exact prefixLift 2109912
  have htrace : WordTrace (prefixWord ++ tailWord_2109912) baseStart_2109912 baseEnd_2109912 := by
    simpa [prefixWord, tailWord_2109912, baseEnd_2109912] using wordTrace_append hprefix tailTrace_2109912
  have hstable : (prefixWord ++ tailWord_2109912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109912).length < 2 ^ (prefixWord ++ tailWord_2109912).sum := by decide
  have hdescent : baseEnd_2109912 < baseStart_2109912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109952 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2109952 : Nat := 118140960795 + 2109952 * 2 ^ 59
def prefixEnd_2109952 : Nat := 4983230072969 + 3 ^ 40 * 2109952 * 2
def baseEnd_2109952 : Nat := 1083419533915434036796513

theorem tailTrace_2109952 : CollatzResearch.WordTrace tailWord_2109952 prefixEnd_2109952 1083419533915434036796513 := by
  unfold tailWord_2109952
  simp only [CollatzResearch.WordTrace]
  refine ⟨38478135826005864978846055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51304181101341153305128073 38478135826005864978846055)
  ·
    refine ⟨57717203739008797468269083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38478135826005864978846055 57717203739008797468269083)
    ·
      refine ⟨86575805608513196202403625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57717203739008797468269083 86575805608513196202403625)
      ·
        refine ⟨64931854206384897151802719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86575805608513196202403625 64931854206384897151802719)
        ·
          refine ⟨97397781309577345727704079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64931854206384897151802719 97397781309577345727704079)
          ·
            refine ⟨146096671964366018591556119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97397781309577345727704079 146096671964366018591556119)
            ·
              refine ⟨219145007946549027887334179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146096671964366018591556119 219145007946549027887334179)
              ·
                refine ⟨328717511919823541831001269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219145007946549027887334179 328717511919823541831001269)
                ·
                  refine ⟨30817266742483457046656369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328717511919823541831001269 30817266742483457046656369)
                  ·
                    refine ⟨23112950056862592784992277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30817266742483457046656369 23112950056862592784992277)
                    ·
                      refine ⟨1083419533915434036796513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23112950056862592784992277 1083419533915434036796513)
                      ·
                        rfl

theorem cell23_2109952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2109952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109952 prefixEnd_2109952 := by exact prefixLift 2109952
  have htrace : WordTrace (prefixWord ++ tailWord_2109952) baseStart_2109952 baseEnd_2109952 := by
    simpa [prefixWord, tailWord_2109952, baseEnd_2109952] using wordTrace_append hprefix tailTrace_2109952
  have hstable : (prefixWord ++ tailWord_2109952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109952).length < 2 ^ (prefixWord ++ tailWord_2109952).sum := by decide
  have hdescent : baseEnd_2109952 < baseStart_2109952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109953 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2109953 : Nat := 118140960795 + 2109953 * 2 ^ 59
def prefixEnd_2109953 : Nat := 4983230072969 + 3 ^ 40 * 2109953 * 2
def baseEnd_2109953 : Nat := 361140015798696177628003

theorem tailTrace_2109953 : CollatzResearch.WordTrace tailWord_2109953 prefixEnd_2109953 361140015798696177628003 := by
  unfold tailWord_2109953
  simp only [CollatzResearch.WordTrace]
  refine ⟨76956308125008107128478513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51304205416672071418985675 76956308125008107128478513)
  ·
    refine ⟨57717231093756080346358885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76956308125008107128478513 57717231093756080346358885)
    ·
      refine ⟨10821980830079265064942291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57717231093756080346358885 10821980830079265064942291)
      ·
        refine ⟨16232971245118897597413437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10821980830079265064942291 16232971245118897597413437)
        ·
          refine ⟨6087364216919586599030039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16232971245118897597413437 6087364216919586599030039)
          ·
            refine ⟨9131046325379379898545059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6087364216919586599030039 9131046325379379898545059)
            ·
              refine ⟨13696569488069069847817589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9131046325379379898545059 13696569488069069847817589)
              ·
                refine ⟨1284053389506475298232899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13696569488069069847817589 1284053389506475298232899)
                ·
                  refine ⟨1926080084259712947349349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284053389506475298232899 1926080084259712947349349)
                  ·
                    refine ⟨361140015798696177628003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926080084259712947349349 361140015798696177628003)
                    ·
                      rfl

theorem cell23_2109953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2109953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109953 prefixEnd_2109953 := by exact prefixLift 2109953
  have htrace : WordTrace (prefixWord ++ tailWord_2109953) baseStart_2109953 baseEnd_2109953 := by
    simpa [prefixWord, tailWord_2109953, baseEnd_2109953] using wordTrace_append hprefix tailTrace_2109953
  have hstable : (prefixWord ++ tailWord_2109953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109953).length < 2 ^ (prefixWord ++ tailWord_2109953).sum := by decide
  have hdescent : baseEnd_2109953 < baseStart_2109953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109966 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_2109966 : Nat := 118140960795 + 2109966 * 2 ^ 59
def prefixEnd_2109966 : Nat := 4983230072969 + 3 ^ 40 * 2109966 * 2
def baseEnd_2109966 : Nat := 120380746960510775780161

theorem tailTrace_2109966 : CollatzResearch.WordTrace tailWord_2109966 prefixEnd_2109966 120380746960510775780161 := by
  unfold tailWord_2109966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619597784245126293587719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51304521515974006899134501 9619597784245126293587719)
  ·
    refine ⟨14429396676367689440381579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9619597784245126293587719 14429396676367689440381579)
    ·
      refine ⟨21644095014551534160572369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14429396676367689440381579 21644095014551534160572369)
      ·
        refine ⟨16233071260913650620429277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21644095014551534160572369 16233071260913650620429277)
        ·
          refine ⟨6087401722842618982660979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16233071260913650620429277 6087401722842618982660979)
          ·
            refine ⟨9131102584263928473991469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6087401722842618982660979 9131102584263928473991469)
            ·
              refine ⟨3424163469098973177746801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9131102584263928473991469 3424163469098973177746801)
              ·
                refine ⟨2568122601824229883310101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3424163469098973177746801 2568122601824229883310101)
                ·
                  refine ⟨120380746960510775780161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2568122601824229883310101 120380746960510775780161)
                  ·
                    rfl

theorem cell23_2109966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_2109966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2109966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2109966 prefixEnd_2109966 := by exact prefixLift 2109966
  have htrace : WordTrace (prefixWord ++ tailWord_2109966) baseStart_2109966 baseEnd_2109966 := by
    simpa [prefixWord, tailWord_2109966, baseEnd_2109966] using wordTrace_append hprefix tailTrace_2109966
  have hstable : (prefixWord ++ tailWord_2109966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109966).length < 2 ^ (prefixWord ++ tailWord_2109966).sum := by decide
  have hdescent : baseEnd_2109966 < baseStart_2109966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110004 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2110004 : Nat := 118140960795 + 2110004 * 2 ^ 59
def prefixEnd_2110004 : Nat := 4983230072969 + 3 ^ 40 * 2110004 * 2
def baseEnd_2110004 : Nat := 361148744969822611115425

theorem tailTrace_2110004 : CollatzResearch.WordTrace tailWord_2110004 prefixEnd_2110004 361148744969822611115425 := by
  unfold tailWord_2110004
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479084123911671419292533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51305445498548895225723377 38479084123911671419292533)
  ·
    refine ⟨3607414136616719195558675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38479084123911671419292533 3607414136616719195558675)
    ·
      refine ⟨5411121204925078793338013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607414136616719195558675 5411121204925078793338013)
      ·
        refine ⟨2029170451846904547501755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5411121204925078793338013 2029170451846904547501755)
        ·
          refine ⟨3043755677770356821252633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029170451846904547501755 3043755677770356821252633)
          ·
            refine ⟨2282816758327767615939475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043755677770356821252633 2282816758327767615939475)
            ·
              refine ⟨3424225137491651423909213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282816758327767615939475 3424225137491651423909213)
              ·
                refine ⟨1284084426559369283965955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3424225137491651423909213 1284084426559369283965955)
                ·
                  refine ⟨1926126639839053925948933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284084426559369283965955 1926126639839053925948933)
                  ·
                    refine ⟨361148744969822611115425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926126639839053925948933 361148744969822611115425)
                    ·
                      rfl

theorem cell23_2110004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2110004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110004 prefixEnd_2110004 := by exact prefixLift 2110004
  have htrace : WordTrace (prefixWord ++ tailWord_2110004) baseStart_2110004 baseEnd_2110004 := by
    simpa [prefixWord, tailWord_2110004, baseEnd_2110004] using wordTrace_append hprefix tailTrace_2110004
  have hstable : (prefixWord ++ tailWord_2110004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110004).length < 2 ^ (prefixWord ++ tailWord_2110004).sum := by decide
  have hdescent : baseEnd_2110004 < baseStart_2110004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110009 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_2110009 : Nat := 118140960795 + 2110009 * 2 ^ 59
def prefixEnd_2110009 : Nat := 4983230072969 + 3 ^ 40 * 2110009 * 2
def baseEnd_2110009 : Nat := 361149600770913437927917

theorem tailTrace_2110009 : CollatzResearch.WordTrace tailWord_2110009 prefixEnd_2110009 361149600770913437927917 := by
  unfold tailWord_2110009
  simp only [CollatzResearch.WordTrace]
  refine ⟨76958350612805228692517081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51305567075203485795011387 76958350612805228692517081)
  ·
    refine ⟨57718762959603921519387811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76958350612805228692517081 57718762959603921519387811)
    ·
      refine ⟨86578144439405882279081717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57718762959603921519387811 86578144439405882279081717)
      ·
        refine ⟨8116701041194301463663911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86578144439405882279081717 8116701041194301463663911)
        ·
          refine ⟨12175051561791452195495867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8116701041194301463663911 12175051561791452195495867)
          ·
            refine ⟨18262577342687178293243801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175051561791452195495867 18262577342687178293243801)
            ·
              refine ⟨13696933007015383719932851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18262577342687178293243801 13696933007015383719932851)
              ·
                refine ⟨20545399510523075579899277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13696933007015383719932851 20545399510523075579899277)
                ·
                  refine ⟨7704524816446153342462229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20545399510523075579899277 7704524816446153342462229)
                  ·
                    refine ⟨361149600770913437927917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7704524816446153342462229 361149600770913437927917)
                    ·
                      rfl

theorem cell23_2110009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_2110009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110009 prefixEnd_2110009 := by exact prefixLift 2110009
  have htrace : WordTrace (prefixWord ++ tailWord_2110009) baseStart_2110009 baseEnd_2110009 := by
    simpa [prefixWord, tailWord_2110009, baseEnd_2110009] using wordTrace_append hprefix tailTrace_2110009
  have hstable : (prefixWord ++ tailWord_2110009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110009).length < 2 ^ (prefixWord ++ tailWord_2110009).sum := by decide
  have hdescent : baseEnd_2110009 < baseStart_2110009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110010 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3]
def baseStart_2110010 : Nat := 118140960795 + 2110010 * 2 ^ 59
def prefixEnd_2110010 : Nat := 4983230072969 + 3 ^ 40 * 2110010 * 2
def baseEnd_2110010 : Nat := 1083449315793394809871247

theorem tailTrace_2110010 : CollatzResearch.WordTrace tailWord_2110010 prefixEnd_2110010 1083449315793394809871247 := by
  unfold tailWord_2110010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19239596771450401465825871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51305591390534403908868989 19239596771450401465825871)
  ·
    refine ⟨28859395157175602198738807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19239596771450401465825871 28859395157175602198738807)
    ·
      refine ⟨43289092735763403298108211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28859395157175602198738807 43289092735763403298108211)
      ·
        refine ⟨64933639103645104947162317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43289092735763403298108211 64933639103645104947162317)
        ·
          refine ⟨24350114663866914355185869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64933639103645104947162317 24350114663866914355185869)
          ·
            refine ⟨9131292998950092883194701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24350114663866914355185869 9131292998950092883194701)
            ·
              refine ⟨3424234874606284831198013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9131292998950092883194701 3424234874606284831198013)
              ·
                refine ⟨1284088077977356811699255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3424234874606284831198013 1284088077977356811699255)
                ·
                  refine ⟨1926132116966035217548883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284088077977356811699255 1926132116966035217548883)
                  ·
                    refine ⟨2889198175449052826323325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926132116966035217548883 2889198175449052826323325)
                    ·
                      refine ⟨1083449315793394809871247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889198175449052826323325 1083449315793394809871247)
                      ·
                        rfl

theorem cell23_2110010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_2110010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110010 prefixEnd_2110010 := by exact prefixLift 2110010
  have htrace : WordTrace (prefixWord ++ tailWord_2110010) baseStart_2110010 baseEnd_2110010 := by
    simpa [prefixWord, tailWord_2110010, baseEnd_2110010] using wordTrace_append hprefix tailTrace_2110010
  have hstable : (prefixWord ++ tailWord_2110010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110010).length < 2 ^ (prefixWord ++ tailWord_2110010).sum := by decide
  have hdescent : baseEnd_2110010 < baseStart_2110010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110016 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_2110016 : Nat := 118140960795 + 2110016 * 2 ^ 59
def prefixEnd_2110016 : Nat := 4983230072969 + 3 ^ 40 * 2110016 * 2
def baseEnd_2110016 : Nat := 1083452396677321786396219

theorem tailTrace_2110016 : CollatzResearch.WordTrace tailWord_2110016 prefixEnd_2110016 1083452396677321786396219 := by
  unfold tailWord_2110016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479302961889934444010951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51305737282519912592014601 38479302961889934444010951)
  ·
    refine ⟨57718954442834901666016427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38479302961889934444010951 57718954442834901666016427)
    ·
      refine ⟨86578431664252352499024641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57718954442834901666016427 86578431664252352499024641)
      ·
        refine ⟨64933823748189264374268481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86578431664252352499024641 64933823748189264374268481)
        ·
          refine ⟨48700367811141948280701361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64933823748189264374268481 48700367811141948280701361)
          ·
            refine ⟨36525275858356461210526021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48700367811141948280701361 36525275858356461210526021)
            ·
              refine ⟨6848489223441836476973629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36525275858356461210526021 6848489223441836476973629)
              ·
                refine ⟨2568183458790688678865111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6848489223441836476973629 2568183458790688678865111)
                ·
                  refine ⟨3852275188186033018297667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568183458790688678865111 3852275188186033018297667)
                  ·
                    refine ⟨5778412782279049527446501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3852275188186033018297667 5778412782279049527446501)
                    ·
                      refine ⟨1083452396677321786396219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5778412782279049527446501 1083452396677321786396219)
                      ·
                        rfl

theorem cell23_2110016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_2110016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110016 prefixEnd_2110016 := by exact prefixLift 2110016
  have htrace : WordTrace (prefixWord ++ tailWord_2110016) baseStart_2110016 baseEnd_2110016 := by
    simpa [prefixWord, tailWord_2110016, baseEnd_2110016] using wordTrace_append hprefix tailTrace_2110016
  have hstable : (prefixWord ++ tailWord_2110016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110016).length < 2 ^ (prefixWord ++ tailWord_2110016).sum := by decide
  have hdescent : baseEnd_2110016 < baseStart_2110016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110026 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_2110026 : Nat := 118140960795 + 2110026 * 2 ^ 59
def prefixEnd_2110026 : Nat := 4983230072969 + 3 ^ 40 * 2110026 * 2
def baseEnd_2110026 : Nat := 361152510494622249090391

theorem tailTrace_2110026 : CollatzResearch.WordTrace tailWord_2110026 prefixEnd_2110026 361152510494622249090391 := by
  unfold tailWord_2110026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19239742663435910148971483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51305980435829093730590621 19239742663435910148971483)
  ·
    refine ⟨28859613995153865223457225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19239742663435910148971483 28859613995153865223457225)
    ·
      refine ⟨21644710496365398917592919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28859613995153865223457225 21644710496365398917592919)
      ·
        refine ⟨32467065744548098376389379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21644710496365398917592919 32467065744548098376389379)
        ·
          refine ⟨48700598616822147564584069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32467065744548098376389379 48700598616822147564584069)
          ·
            refine ⟨9131362240654152668359513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48700598616822147564584069 9131362240654152668359513)
            ·
              refine ⟨6848521680490614501269635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9131362240654152668359513 6848521680490614501269635)
              ·
                refine ⟨10272782520735921751904453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848521680490614501269635 10272782520735921751904453)
                ·
                  refine ⟨1926146722637985328482085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10272782520735921751904453 1926146722637985328482085)
                  ·
                    refine ⟨361152510494622249090391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926146722637985328482085 361152510494622249090391)
                    ·
                      rfl

theorem cell23_2110026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_2110026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110026 prefixEnd_2110026 := by exact prefixLift 2110026
  have htrace : WordTrace (prefixWord ++ tailWord_2110026) baseStart_2110026 baseEnd_2110026 := by
    simpa [prefixWord, tailWord_2110026, baseEnd_2110026] using wordTrace_append hprefix tailTrace_2110026
  have hstable : (prefixWord ++ tailWord_2110026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110026).length < 2 ^ (prefixWord ++ tailWord_2110026).sum := by decide
  have hdescent : baseEnd_2110026 < baseStart_2110026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110036 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2110036 : Nat := 118140960795 + 2110036 * 2 ^ 59
def prefixEnd_2110036 : Nat := 4983230072969 + 3 ^ 40 * 2110036 * 2
def baseEnd_2110036 : Nat := 1083462666290411708146127

theorem tailTrace_2110036 : CollatzResearch.WordTrace tailWord_2110036 prefixEnd_2110036 1083462666290411708146127 := by
  unfold tailWord_2110036
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479667691853706151874981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51306223589138274869166641 38479667691853706151874981)
  ·
    refine ⟨7214937692222569903476559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38479667691853706151874981 7214937692222569903476559)
    ·
      refine ⟨10822406538333854855214839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214937692222569903476559 10822406538333854855214839)
      ·
        refine ⟨16233609807500782282822259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10822406538333854855214839 16233609807500782282822259)
        ·
          refine ⟨24350414711251173424233389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16233609807500782282822259 24350414711251173424233389)
          ·
            refine ⟨9131405516719190034087521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24350414711251173424233389 9131405516719190034087521)
            ·
              refine ⟨6848554137539392525565641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9131405516719190034087521 6848554137539392525565641)
              ·
                refine ⟨5136415603154544394174231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6848554137539392525565641 5136415603154544394174231)
                ·
                  refine ⟨7704623404731816591261347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136415603154544394174231 7704623404731816591261347)
                  ·
                    refine ⟨11556935107097724886892021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7704623404731816591261347 11556935107097724886892021)
                    ·
                      refine ⟨1083462666290411708146127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11556935107097724886892021 1083462666290411708146127)
                      ·
                        rfl

theorem cell23_2110036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2110036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110036 prefixEnd_2110036 := by exact prefixLift 2110036
  have htrace : WordTrace (prefixWord ++ tailWord_2110036) baseStart_2110036 baseEnd_2110036 := by
    simpa [prefixWord, tailWord_2110036, baseEnd_2110036] using wordTrace_append hprefix tailTrace_2110036
  have hstable : (prefixWord ++ tailWord_2110036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110036).length < 2 ^ (prefixWord ++ tailWord_2110036).sum := by decide
  have hdescent : baseEnd_2110036 < baseStart_2110036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110039 : List Nat := [1, 1, 3, 2, 2, 2, 4, 8]
def baseStart_2110039 : Nat := 118140960795 + 2110039 * 2 ^ 59
def prefixEnd_2110039 : Nat := 4983230072969 + 3 ^ 40 * 2110039 * 2
def baseEnd_2110039 : Nat := 40128303953050933200319

theorem tailTrace_2110039 : CollatzResearch.WordTrace tailWord_2110039 prefixEnd_2110039 40128303953050933200319 := by
  unfold tailWord_2110039
  simp only [CollatzResearch.WordTrace]
  refine ⟨76959444802696543816109171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51306296535131029210739447 76959444802696543816109171)
  ·
    refine ⟨115439167204044815724163757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76959444802696543816109171 115439167204044815724163757)
    ·
      refine ⟨43289687701516805896561409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115439167204044815724163757 43289687701516805896561409)
      ·
        refine ⟨32467265776137604422421057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43289687701516805896561409 32467265776137604422421057)
        ·
          refine ⟨24350449332103203316815793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32467265776137604422421057 24350449332103203316815793)
          ·
            refine ⟨18262836999077402487611845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24350449332103203316815793 18262836999077402487611845)
            ·
              refine ⟨3424281937327012966427221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18262836999077402487611845 3424281937327012966427221)
              ·
                refine ⟨40128303953050933200319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3424281937327012966427221 40128303953050933200319)
                ·
                  rfl

theorem cell23_2110039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 8].length) (baseStart_2110039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110039 prefixEnd_2110039 := by exact prefixLift 2110039
  have htrace : WordTrace (prefixWord ++ tailWord_2110039) baseStart_2110039 baseEnd_2110039 := by
    simpa [prefixWord, tailWord_2110039, baseEnd_2110039] using wordTrace_append hprefix tailTrace_2110039
  have hstable : (prefixWord ++ tailWord_2110039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110039).length < 2 ^ (prefixWord ++ tailWord_2110039).sum := by decide
  have hdescent : baseEnd_2110039 < baseStart_2110039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110050 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2110050 : Nat := 118140960795 + 2110050 * 2 ^ 59
def prefixEnd_2110050 : Nat := 4983230072969 + 3 ^ 40 * 2110050 * 2
def baseEnd_2110050 : Nat := 1083469855019574653371063

theorem tailTrace_2110050 : CollatzResearch.WordTrace tailWord_2110050 prefixEnd_2110050 1083469855019574653371063 := by
  unfold tailWord_2110050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19239961501414173173689901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51306564003771128463173069 19239961501414173173689901)
  ·
    refine ⟨7214985563030314940133713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19239961501414173173689901 7214985563030314940133713)
    ·
      refine ⟨5411239172272736205100285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7214985563030314940133713 5411239172272736205100285)
      ·
        refine ⟨2029214689602276076912607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5411239172272736205100285 2029214689602276076912607)
        ·
          refine ⟨3043822034403414115368911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029214689602276076912607 3043822034403414115368911)
          ·
            refine ⟨4565733051605121173053367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043822034403414115368911 4565733051605121173053367)
            ·
              refine ⟨6848599577407681759580051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565733051605121173053367 6848599577407681759580051)
              ·
                refine ⟨10272899366111522639370077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848599577407681759580051 10272899366111522639370077)
                ·
                  refine ⟨3852337262291820989763779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10272899366111522639370077 3852337262291820989763779)
                  ·
                    refine ⟨5778505893437731484645669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3852337262291820989763779 5778505893437731484645669)
                    ·
                      refine ⟨1083469855019574653371063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5778505893437731484645669 1083469855019574653371063)
                      ·
                        rfl

theorem cell23_2110050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2110050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110050 prefixEnd_2110050 := by exact prefixLift 2110050
  have htrace : WordTrace (prefixWord ++ tailWord_2110050) baseStart_2110050 baseEnd_2110050 := by
    simpa [prefixWord, tailWord_2110050, baseEnd_2110050] using wordTrace_append hprefix tailTrace_2110050
  have hstable : (prefixWord ++ tailWord_2110050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110050).length < 2 ^ (prefixWord ++ tailWord_2110050).sum := by decide
  have hdescent : baseEnd_2110050 < baseStart_2110050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110053 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2110053 : Nat := 118140960795 + 2110053 * 2 ^ 59
def prefixEnd_2110053 : Nat := 4983230072969 + 3 ^ 40 * 2110053 * 2
def baseEnd_2110053 : Nat := 1083471395461538141633549

theorem tailTrace_2110053 : CollatzResearch.WordTrace tailWord_2110053 prefixEnd_2110053 1083471395461538141633549 := by
  unfold tailWord_2110053
  simp only [CollatzResearch.WordTrace]
  refine ⟨76959955424645824207118813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51306636949763882804745875 76959955424645824207118813)
  ·
    refine ⟨28859983284242184077669555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76959955424645824207118813 28859983284242184077669555)
    ·
      refine ⟨43289974926363276116504333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28859983284242184077669555 43289974926363276116504333)
      ·
        refine ⟨16233740597386228543689125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43289974926363276116504333 16233740597386228543689125)
        ·
          refine ⟨3043826362009917851941711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16233740597386228543689125 3043826362009917851941711)
          ·
            refine ⟨4565739543014876777912567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043826362009917851941711 4565739543014876777912567)
            ·
              refine ⟨6848609314522315166868851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565739543014876777912567 6848609314522315166868851)
              ·
                refine ⟨10272913971783472750303277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848609314522315166868851 10272913971783472750303277)
                ·
                  refine ⟨3852342739418802281363729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10272913971783472750303277 3852342739418802281363729)
                  ·
                    refine ⟨2889257054564101711022797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3852342739418802281363729 2889257054564101711022797)
                    ·
                      refine ⟨1083471395461538141633549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889257054564101711022797 1083471395461538141633549)
                      ·
                        rfl

theorem cell23_2110053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2110053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110053 prefixEnd_2110053 := by exact prefixLift 2110053
  have htrace : WordTrace (prefixWord ++ tailWord_2110053) baseStart_2110053 baseEnd_2110053 := by
    simpa [prefixWord, tailWord_2110053, baseEnd_2110053] using wordTrace_append hprefix tailTrace_2110053
  have hstable : (prefixWord ++ tailWord_2110053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110053).length < 2 ^ (prefixWord ++ tailWord_2110053).sum := by decide
  have hdescent : baseEnd_2110053 < baseStart_2110053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110070 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2110070 : Nat := 118140960795 + 2110070 * 2 ^ 59
def prefixEnd_2110070 : Nat := 4983230072969 + 3 ^ 40 * 2110070 * 2
def baseEnd_2110070 : Nat := 1083480124632664575120971

theorem tailTrace_2110070 : CollatzResearch.WordTrace tailWord_2110070 prefixEnd_2110070 1083480124632664575120971 := by
  unfold tailWord_2110070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810035966599014756905479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51307050310389490740325109 4810035966599014756905479)
  ·
    refine ⟨7215053949898522135358219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810035966599014756905479 7215053949898522135358219)
    ·
      refine ⟨10822580924847783203037329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215053949898522135358219 10822580924847783203037329)
      ·
        refine ⟨8116935693635837402277997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10822580924847783203037329 8116935693635837402277997)
        ·
          refine ⟨3043850885113439025854249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8116935693635837402277997 3043850885113439025854249)
          ·
            refine ⟨2282888163835079269390687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043850885113439025854249 2282888163835079269390687)
            ·
              refine ⟨3424332245752618904086031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282888163835079269390687 3424332245752618904086031)
              ·
                refine ⟨5136498368628928356129047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424332245752618904086031 5136498368628928356129047)
                ·
                  refine ⟨7704747552943392534193571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136498368628928356129047 7704747552943392534193571)
                  ·
                    refine ⟨11557121329415088801290357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7704747552943392534193571 11557121329415088801290357)
                    ·
                      refine ⟨1083480124632664575120971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11557121329415088801290357 1083480124632664575120971)
                      ·
                        rfl

theorem cell23_2110070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2110070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110070 prefixEnd_2110070 := by exact prefixLift 2110070
  have htrace : WordTrace (prefixWord ++ tailWord_2110070) baseStart_2110070 baseEnd_2110070 := by
    simpa [prefixWord, tailWord_2110070, baseEnd_2110070] using wordTrace_append hprefix tailTrace_2110070
  have hstable : (prefixWord ++ tailWord_2110070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110070).length < 2 ^ (prefixWord ++ tailWord_2110070).sum := by decide
  have hdescent : baseEnd_2110070 < baseStart_2110070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110083 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 3]
def baseStart_2110083 : Nat := 118140960795 + 2110083 * 2 ^ 59
def prefixEnd_2110083 : Nat := 4983230072969 + 3 ^ 40 * 2110083 * 2
def baseEnd_2110083 : Nat := 1083486799881173024258411

theorem tailTrace_2110083 : CollatzResearch.WordTrace tailWord_2110083 prefixEnd_2110083 1083486799881173024258411 := by
  unfold tailWord_2110083
  simp only [CollatzResearch.WordTrace]
  refine ⟨76961049614537139330710903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51307366409691426220473935 76961049614537139330710903)
  ·
    refine ⟨115441574421805708996066355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76961049614537139330710903 115441574421805708996066355)
    ·
      refine ⟨173162361632708563494099533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115441574421805708996066355 173162361632708563494099533)
      ·
        refine ⟨64935885612265711310287325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173162361632708563494099533 64935885612265711310287325)
        ·
          refine ⟨24350957104599641741357747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64935885612265711310287325 24350957104599641741357747)
          ·
            refine ⟨36526435656899462612036621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24350957104599641741357747 36526435656899462612036621)
            ·
              refine ⟨13697413371337298479513733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36526435656899462612036621 13697413371337298479513733)
              ·
                refine ⟨2568265007125743464908825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13697413371337298479513733 2568265007125743464908825)
                ·
                  refine ⟨1926198755344307598681619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2568265007125743464908825 1926198755344307598681619)
                  ·
                    refine ⟨2889298133016461398022429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926198755344307598681619 2889298133016461398022429)
                    ·
                      refine ⟨1083486799881173024258411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889298133016461398022429 1083486799881173024258411)
                      ·
                        rfl

theorem cell23_2110083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_2110083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110083 prefixEnd_2110083 := by exact prefixLift 2110083
  have htrace : WordTrace (prefixWord ++ tailWord_2110083) baseStart_2110083 baseEnd_2110083 := by
    simpa [prefixWord, tailWord_2110083, baseEnd_2110083] using wordTrace_append hprefix tailTrace_2110083
  have hstable : (prefixWord ++ tailWord_2110083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110083).length < 2 ^ (prefixWord ++ tailWord_2110083).sum := by decide
  have hdescent : baseEnd_2110083 < baseStart_2110083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110084 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_2110084 : Nat := 118140960795 + 2110084 * 2 ^ 59
def prefixEnd_2110084 : Nat := 4983230072969 + 3 ^ 40 * 2110084 * 2
def baseEnd_2110084 : Nat := 1083487313361827520345907

theorem tailTrace_2110084 : CollatzResearch.WordTrace tailWord_2110084 prefixEnd_2110084 1083487313361827520345907 := by
  unfold tailWord_2110084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38480543043766758250748653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51307390725022344334331537 38480543043766758250748653)
  ·
    refine ⟨14430203641412534344030745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38480543043766758250748653 14430203641412534344030745)
    ·
      refine ⟨10822652731059400758023059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14430203641412534344030745 10822652731059400758023059)
      ·
        refine ⟨16233979096589101137034589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10822652731059400758023059 16233979096589101137034589)
        ·
          refine ⟨6087742161220912926387971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16233979096589101137034589 6087742161220912926387971)
          ·
            refine ⟨9131613241831369389581957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6087742161220912926387971 9131613241831369389581957)
            ·
              refine ⟨1712177482843381760546617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9131613241831369389581957 1712177482843381760546617)
              ·
                refine ⟨1284133112132536320409963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712177482843381760546617 1284133112132536320409963)
                ·
                  refine ⟨1926199668198804480614945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284133112132536320409963 1926199668198804480614945)
                  ·
                    refine ⟨1444649751149103360461209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1926199668198804480614945 1444649751149103360461209)
                    ·
                      refine ⟨1083487313361827520345907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444649751149103360461209 1083487313361827520345907)
                      ·
                        rfl

theorem cell23_2110084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_2110084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110084 prefixEnd_2110084 := by exact prefixLift 2110084
  have htrace : WordTrace (prefixWord ++ tailWord_2110084) baseStart_2110084 baseEnd_2110084 := by
    simpa [prefixWord, tailWord_2110084, baseEnd_2110084] using wordTrace_append hprefix tailTrace_2110084
  have hstable : (prefixWord ++ tailWord_2110084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110084).length < 2 ^ (prefixWord ++ tailWord_2110084).sum := by decide
  have hdescent : baseEnd_2110084 < baseStart_2110084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110099 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 2, 6]
def baseStart_2110099 : Nat := 118140960795 + 2110099 * 2 ^ 59
def prefixEnd_2110099 : Nat := 4983230072969 + 3 ^ 40 * 2110099 * 2
def baseEnd_2110099 : Nat := 361165005190548320552779

theorem tailTrace_2110099 : CollatzResearch.WordTrace tailWord_2110099 prefixEnd_2110099 361165005190548320552779 := by
  unfold tailWord_2110099
  simp only [CollatzResearch.WordTrace]
  refine ⟨76961633182479174063293351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51307755454986116042195567 76961633182479174063293351)
  ·
    refine ⟨115442449773718761094940027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76961633182479174063293351 115442449773718761094940027)
    ·
      refine ⟨173163674660578141642410041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115442449773718761094940027 173163674660578141642410041)
      ·
        refine ⟨129872755995433606231807531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173163674660578141642410041 129872755995433606231807531)
        ·
          refine ⟨194809133993150409347711297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129872755995433606231807531 194809133993150409347711297)
          ·
            refine ⟨146106850494862807010783473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194809133993150409347711297 146106850494862807010783473)
            ·
              refine ⟨109580137871147105258087605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146106850494862807010783473 109580137871147105258087605)
              ·
                refine ⟨10273137925420041117945713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109580137871147105258087605 10273137925420041117945713)
                ·
                  refine ⟨7704853444065030838459285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10273137925420041117945713 7704853444065030838459285)
                  ·
                    refine ⟨361165005190548320552779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7704853444065030838459285 361165005190548320552779)
                    ·
                      rfl

theorem cell23_2110099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_2110099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110099 prefixEnd_2110099 := by exact prefixLift 2110099
  have htrace : WordTrace (prefixWord ++ tailWord_2110099) baseStart_2110099 baseEnd_2110099 := by
    simpa [prefixWord, tailWord_2110099, baseEnd_2110099] using wordTrace_append hprefix tailTrace_2110099
  have hstable : (prefixWord ++ tailWord_2110099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110099).length < 2 ^ (prefixWord ++ tailWord_2110099).sum := by decide
  have hdescent : baseEnd_2110099 < baseStart_2110099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110100 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2110100 : Nat := 118140960795 + 2110100 * 2 ^ 59
def prefixEnd_2110100 : Nat := 4983230072969 + 3 ^ 40 * 2110100 * 2
def baseEnd_2110100 : Nat := 1083495529052299457745833

theorem tailTrace_2110100 : CollatzResearch.WordTrace tailWord_2110100 prefixEnd_2110100 1083495529052299457745833 := by
  unfold tailWord_2110100
  simp only [CollatzResearch.WordTrace]
  refine ⟨38480834827737775617039877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51307779770317034156053169 38480834827737775617039877)
  ·
    refine ⟨7215156530200832928194977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38480834827737775617039877 7215156530200832928194977)
    ·
      refine ⟨5411367397650624696146233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7215156530200832928194977 5411367397650624696146233)
      ·
        refine ⟨4058525548237968522109675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5411367397650624696146233 4058525548237968522109675)
        ·
          refine ⟨6087788322356952783164513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4058525548237968522109675 6087788322356952783164513)
          ·
            refine ⟨4565841241767714587373385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6087788322356952783164513 4565841241767714587373385)
            ·
              refine ⟨3424380931325785940530039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4565841241767714587373385 3424380931325785940530039)
              ·
                refine ⟨5136571396988678910795059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424380931325785940530039 5136571396988678910795059)
                ·
                  refine ⟨7704857095483018366192589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136571396988678910795059 7704857095483018366192589)
                  ·
                    refine ⟨2889321410806131887322221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7704857095483018366192589 2889321410806131887322221)
                    ·
                      refine ⟨1083495529052299457745833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889321410806131887322221 1083495529052299457745833)
                      ·
                        rfl

theorem cell23_2110100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2110100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110100 prefixEnd_2110100 := by exact prefixLift 2110100
  have htrace : WordTrace (prefixWord ++ tailWord_2110100) baseStart_2110100 baseEnd_2110100 := by
    simpa [prefixWord, tailWord_2110100, baseEnd_2110100] using wordTrace_append hprefix tailTrace_2110100
  have hstable : (prefixWord ++ tailWord_2110100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110100).length < 2 ^ (prefixWord ++ tailWord_2110100).sum := by decide
  have hdescent : baseEnd_2110100 < baseStart_2110100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110110 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_2110110 : Nat := 118140960795 + 2110110 * 2 ^ 59
def prefixEnd_2110110 : Nat := 4983230072969 + 3 ^ 40 * 2110110 * 2
def baseEnd_2110110 : Nat := 1083500663858844418620787

theorem tailTrace_2110110 : CollatzResearch.WordTrace tailWord_2110110 prefixEnd_2110110 1083500663858844418620787 := by
  unfold tailWord_2110110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9620254298179915367742973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51308022923626215294629189 9620254298179915367742973)
  ·
    refine ⟨3607595361817468262903615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9620254298179915367742973 3607595361817468262903615)
    ·
      refine ⟨5411393042726202394355423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607595361817468262903615 5411393042726202394355423)
      ·
        refine ⟨8117089564089303591533135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5411393042726202394355423 8117089564089303591533135)
        ·
          refine ⟨12175634346133955387299703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117089564089303591533135 12175634346133955387299703)
          ·
            refine ⟨18263451519200933080949555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175634346133955387299703 18263451519200933080949555)
            ·
              refine ⟨27395177278801399621424333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18263451519200933080949555 27395177278801399621424333)
              ·
                refine ⟨10273191479550524858034125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27395177278801399621424333 10273191479550524858034125)
                ·
                  refine ⟨3852446804831446821762797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10273191479550524858034125 3852446804831446821762797)
                  ·
                    refine ⟨1444667551811792558161049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3852446804831446821762797 1444667551811792558161049)
                    ·
                      refine ⟨1083500663858844418620787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444667551811792558161049 1083500663858844418620787)
                      ·
                        rfl

theorem cell23_2110110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_2110110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110110 prefixEnd_2110110 := by exact prefixLift 2110110
  have htrace : WordTrace (prefixWord ++ tailWord_2110110) baseStart_2110110 baseEnd_2110110 := by
    simpa [prefixWord, tailWord_2110110, baseEnd_2110110] using wordTrace_append hprefix tailTrace_2110110
  have hstable : (prefixWord ++ tailWord_2110110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110110).length < 2 ^ (prefixWord ++ tailWord_2110110).sum := by decide
  have hdescent : baseEnd_2110110 < baseStart_2110110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110127 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 1, 3, 2]
def baseStart_2110127 : Nat := 118140960795 + 2110127 * 2 ^ 59
def prefixEnd_2110127 : Nat := 4983230072969 + 3 ^ 40 * 2110127 * 2
def baseEnd_2110127 : Nat := 1083509393029970852108209

theorem tailTrace_2110127 : CollatzResearch.WordTrace tailWord_2110127 prefixEnd_2110127 1083509393029970852108209 := by
  unfold tailWord_2110127
  simp only [CollatzResearch.WordTrace]
  refine ⟨76962654426377734845312635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51308436284251823230208423 76962654426377734845312635)
  ·
    refine ⟨115443981639566602267968953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76962654426377734845312635 115443981639566602267968953)
    ·
      refine ⟨86582986229674951700976715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115443981639566602267968953 86582986229674951700976715)
      ·
        refine ⟨129874479344512427551465073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86582986229674951700976715 129874479344512427551465073)
        ·
          refine ⟨97405859508384320663598805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129874479344512427551465073 97405859508384320663598805)
          ·
            refine ⟨2282949832227757515553097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 97405859508384320663598805 2282949832227757515553097)
            ·
              refine ⟨1712212374170818136664823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282949832227757515553097 1712212374170818136664823)
              ·
                refine ⟨2568318561256227204997235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712212374170818136664823 2568318561256227204997235)
                ·
                  refine ⟨3852477841884340807495853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568318561256227204997235 3852477841884340807495853)
                  ·
                    refine ⟨1444679190706627802810945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3852477841884340807495853 1444679190706627802810945)
                    ·
                      refine ⟨1083509393029970852108209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444679190706627802810945 1083509393029970852108209)
                      ·
                        rfl

theorem cell23_2110127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 3, 2].length) (baseStart_2110127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110127 prefixEnd_2110127 := by exact prefixLift 2110127
  have htrace : WordTrace (prefixWord ++ tailWord_2110127) baseStart_2110127 baseEnd_2110127 := by
    simpa [prefixWord, tailWord_2110127, baseEnd_2110127] using wordTrace_append hprefix tailTrace_2110127
  have hstable : (prefixWord ++ tailWord_2110127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110127).length < 2 ^ (prefixWord ++ tailWord_2110127).sum := by decide
  have hdescent : baseEnd_2110127 < baseStart_2110127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110140 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_2110140 : Nat := 118140960795 + 2110140 * 2 ^ 59
def prefixEnd_2110140 : Nat := 4983230072969 + 3 ^ 40 * 2110140 * 2
def baseEnd_2110140 : Nat := 1083516068278479301245649

theorem tailTrace_2110140 : CollatzResearch.WordTrace tailWord_2110140 prefixEnd_2110140 1083516068278479301245649 := by
  unfold tailWord_2110140
  simp only [CollatzResearch.WordTrace]
  refine ⟨38481564287665319032767937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51308752383553758710357249 38481564287665319032767937)
  ·
    refine ⟨28861173215748989274575953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38481564287665319032767937 28861173215748989274575953)
    ·
      refine ⟨21645879911811741955931965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28861173215748989274575953 21645879911811741955931965)
      ·
        refine ⟨8117204966929403233474487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21645879911811741955931965 8117204966929403233474487)
        ·
          refine ⟨12175807450394104850211731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117204966929403233474487 12175807450394104850211731)
          ·
            refine ⟨18263711175591157275317597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175807450394104850211731 18263711175591157275317597)
            ·
              refine ⟨6848891690846683978244099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18263711175591157275317597 6848891690846683978244099)
              ·
                refine ⟨10273337536270025967366149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6848891690846683978244099 10273337536270025967366149)
                ·
                  refine ⟨1926250788050629868881153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10273337536270025967366149 1926250788050629868881153)
                  ·
                    refine ⟨1444688091037972401660865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1926250788050629868881153 1444688091037972401660865)
                    ·
                      refine ⟨1083516068278479301245649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444688091037972401660865 1083516068278479301245649)
                      ·
                        rfl

theorem cell23_2110140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_2110140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110140 prefixEnd_2110140 := by exact prefixLift 2110140
  have htrace : WordTrace (prefixWord ++ tailWord_2110140) baseStart_2110140 baseEnd_2110140 := by
    simpa [prefixWord, tailWord_2110140, baseEnd_2110140] using wordTrace_append hprefix tailTrace_2110140
  have hstable : (prefixWord ++ tailWord_2110140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110140).length < 2 ^ (prefixWord ++ tailWord_2110140).sum := by decide
  have hdescent : baseEnd_2110140 < baseStart_2110140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110149 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_2110149 : Nat := 118140960795 + 2110149 * 2 ^ 59
def prefixEnd_2110149 : Nat := 4983230072969 + 3 ^ 40 * 2110149 * 2
def baseEnd_2110149 : Nat := 1083520689604369766033107

theorem tailTrace_2110149 : CollatzResearch.WordTrace tailWord_2110149 prefixEnd_2110149 1083520689604369766033107 := by
  unfold tailWord_2110149
  simp only [CollatzResearch.WordTrace]
  refine ⟨76963456832298032602613501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51308971221532021735075667 76963456832298032602613501)
  ·
    refine ⟨28861296312111762225980063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76963456832298032602613501 28861296312111762225980063)
    ·
      refine ⟨43291944468167643338970095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28861296312111762225980063 43291944468167643338970095)
      ·
        refine ⟨64937916702251465008455143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43291944468167643338970095 64937916702251465008455143)
        ·
          refine ⟨97406875053377197512682715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64937916702251465008455143 97406875053377197512682715)
          ·
            refine ⟨146110312580065796269024073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97406875053377197512682715 146110312580065796269024073)
            ·
              refine ⟨109582734435049347201768055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146110312580065796269024073 109582734435049347201768055)
              ·
                refine ⟨164374101652574020802652083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109582734435049347201768055 164374101652574020802652083)
                ·
                  refine ⟨246561152478861031203978125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164374101652574020802652083 246561152478861031203978125)
                  ·
                    refine ⟨92460432179572886701491797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246561152478861031203978125 92460432179572886701491797)
                    ·
                      refine ⟨1083520689604369766033107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92460432179572886701491797 1083520689604369766033107)
                      ·
                        rfl

theorem cell23_2110149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_2110149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110149 prefixEnd_2110149 := by exact prefixLift 2110149
  have htrace : WordTrace (prefixWord ++ tailWord_2110149) baseStart_2110149 baseEnd_2110149 := by
    simpa [prefixWord, tailWord_2110149, baseEnd_2110149] using wordTrace_append hprefix tailTrace_2110149
  have hstable : (prefixWord ++ tailWord_2110149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110149).length < 2 ^ (prefixWord ++ tailWord_2110149).sum := by decide
  have hdescent : baseEnd_2110149 < baseStart_2110149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110176 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_2110176 : Nat := 118140960795 + 2110176 * 2 ^ 59
def prefixEnd_2110176 : Nat := 4983230072969 + 3 ^ 40 * 2110176 * 2
def baseEnd_2110176 : Nat := 361178184527347053465161

theorem tailTrace_2110176 : CollatzResearch.WordTrace tailWord_2110176 prefixEnd_2110176 361178184527347053465161 := by
  unfold tailWord_2110176
  simp only [CollatzResearch.WordTrace]
  refine ⟨38482220801600108106923191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51309627735466810809230921 38482220801600108106923191)
  ·
    refine ⟨57723331202400162160384787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38482220801600108106923191 57723331202400162160384787)
    ·
      refine ⟨86584996803600243240577181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57723331202400162160384787 86584996803600243240577181)
      ·
        refine ⟨32469373801350091215216443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86584996803600243240577181 32469373801350091215216443)
        ·
          refine ⟨48704060702025136822824665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32469373801350091215216443 48704060702025136822824665)
          ·
            refine ⟨36528045526518852617118499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48704060702025136822824665 36528045526518852617118499)
            ·
              refine ⟨54792068289778278925677749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36528045526518852617118499 54792068289778278925677749)
              ·
                refine ⟨5136756402166713649282289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54792068289778278925677749 5136756402166713649282289)
                ·
                  refine ⟨3852567301625035236961717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5136756402166713649282289 3852567301625035236961717)
                  ·
                    refine ⟨361178184527347053465161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3852567301625035236961717 361178184527347053465161)
                    ·
                      rfl

theorem cell23_2110176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_2110176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110176 prefixEnd_2110176 := by exact prefixLift 2110176
  have htrace : WordTrace (prefixWord ++ tailWord_2110176) baseStart_2110176 baseEnd_2110176 := by
    simpa [prefixWord, tailWord_2110176, baseEnd_2110176] using wordTrace_append hprefix tailTrace_2110176
  have hstable : (prefixWord ++ tailWord_2110176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110176).length < 2 ^ (prefixWord ++ tailWord_2110176).sum := by decide
  have hdescent : baseEnd_2110176 < baseStart_2110176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110180 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 5]
def baseStart_2110180 : Nat := 118140960795 + 2110180 * 2 ^ 59
def prefixEnd_2110180 : Nat := 4983230072969 + 3 ^ 40 * 2110180 * 2
def baseEnd_2110180 : Nat := 120392956389406571638385

theorem tailTrace_2110180 : CollatzResearch.WordTrace tailWord_2110180 prefixEnd_2110180 120392956389406571638385 := by
  unfold tailWord_2110180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38482293747592862448495997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51309724996790483264661329 38482293747592862448495997)
  ·
    refine ⟨14430860155347323418185999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38482293747592862448495997 14430860155347323418185999)
    ·
      refine ⟨21646290233020985127278999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14430860155347323418185999 21646290233020985127278999)
      ·
        refine ⟨32469435349531477690918499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21646290233020985127278999 32469435349531477690918499)
        ·
          refine ⟨48704153024297216536377749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32469435349531477690918499 48704153024297216536377749)
          ·
            refine ⟨2283007173013932025142707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48704153024297216536377749 2283007173013932025142707)
            ·
              refine ⟨3424510759520898037714061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283007173013932025142707 3424510759520898037714061)
              ·
                refine ⟨1284191534820336764142773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3424510759520898037714061 1284191534820336764142773)
                ·
                  refine ⟨120392956389406571638385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1284191534820336764142773 120392956389406571638385)
                  ·
                    rfl

theorem cell23_2110180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_2110180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110180 prefixEnd_2110180 := by exact prefixLift 2110180
  have htrace : WordTrace (prefixWord ++ tailWord_2110180) baseStart_2110180 baseEnd_2110180 := by
    simpa [prefixWord, tailWord_2110180, baseEnd_2110180] using wordTrace_append hprefix tailTrace_2110180
  have hstable : (prefixWord ++ tailWord_2110180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110180).length < 2 ^ (prefixWord ++ tailWord_2110180).sum := by decide
  have hdescent : baseEnd_2110180 < baseStart_2110180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110186 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2110186 : Nat := 118140960795 + 2110186 * 2 ^ 59
def prefixEnd_2110186 : Nat := 4983230072969 + 3 ^ 40 * 2110186 * 2
def baseEnd_2110186 : Nat := 1083539688388586121270437

theorem tailTrace_2110186 : CollatzResearch.WordTrace tailWord_2110186 prefixEnd_2110186 1083539688388586121270437 := by
  unfold tailWord_2110186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19241201583290996980427603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51309870888775991947806941 19241201583290996980427603)
  ·
    refine ⟨28861802374936495470641405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19241201583290996980427603 28861802374936495470641405)
    ·
      refine ⟨10823175890601185801490527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28861802374936495470641405 10823175890601185801490527)
      ·
        refine ⟨16234763835901778702235791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10823175890601185801490527 16234763835901778702235791)
        ·
          refine ⟨24352145753852668053353687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16234763835901778702235791 24352145753852668053353687)
          ·
            refine ⟨36528218630779002080030531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24352145753852668053353687 36528218630779002080030531)
            ·
              refine ⟨54792327946168503120045797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36528218630779002080030531 54792327946168503120045797)
              ·
                refine ⟨10273561489906594335008587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54792327946168503120045797 10273561489906594335008587)
                ·
                  refine ⟨15410342234859891502512881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10273561489906594335008587 15410342234859891502512881)
                  ·
                    refine ⟨11557756676144918626884661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15410342234859891502512881 11557756676144918626884661)
                    ·
                      refine ⟨1083539688388586121270437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11557756676144918626884661 1083539688388586121270437)
                      ·
                        rfl

theorem cell23_2110186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2110186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110186 prefixEnd_2110186 := by exact prefixLift 2110186
  have htrace : WordTrace (prefixWord ++ tailWord_2110186) baseStart_2110186 baseEnd_2110186 := by
    simpa [prefixWord, tailWord_2110186, baseEnd_2110186] using wordTrace_append hprefix tailTrace_2110186
  have hstable : (prefixWord ++ tailWord_2110186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110186).length < 2 ^ (prefixWord ++ tailWord_2110186).sum := by decide
  have hdescent : baseEnd_2110186 < baseStart_2110186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110213 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_2110213 : Nat := 118140960795 + 2110213 * 2 ^ 59
def prefixEnd_2110213 : Nat := 4983230072969 + 3 ^ 40 * 2110213 * 2
def baseEnd_2110213 : Nat := 1083553552366257515632813

theorem tailTrace_2110213 : CollatzResearch.WordTrace tailWord_2110213 prefixEnd_2110213 1083553552366257515632813 := by
  unfold tailWord_2110213
  simp only [CollatzResearch.WordTrace]
  refine ⟨76965791104066171532943293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51310527402710781021962195 76965791104066171532943293)
  ·
    refine ⟨28862171664024814324853735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76965791104066171532943293 28862171664024814324853735)
    ·
      refine ⟨43293257496037221487280603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28862171664024814324853735 43293257496037221487280603)
      ·
        refine ⟨64939886244055832230920905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43293257496037221487280603 64939886244055832230920905)
        ·
          refine ⟨48704914683041874173190679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64939886244055832230920905 48704914683041874173190679)
          ·
            refine ⟨73057372024562811259786019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48704914683041874173190679 73057372024562811259786019)
            ·
              refine ⟨109586058036844216889679029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73057372024562811259786019 109586058036844216889679029)
              ·
                refine ⟨10273692940954145333407409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109586058036844216889679029 10273692940954145333407409)
                ·
                  refine ⟨7705269705715609000055557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10273692940954145333407409 7705269705715609000055557)
                  ·
                    refine ⟨1444738069821676687510417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7705269705715609000055557 1444738069821676687510417)
                    ·
                      refine ⟨1083553552366257515632813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444738069821676687510417 1083553552366257515632813)
                      ·
                        rfl

theorem cell23_2110213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_2110213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110213 prefixEnd_2110213 := by exact prefixLift 2110213
  have htrace : WordTrace (prefixWord ++ tailWord_2110213) baseStart_2110213 baseEnd_2110213 := by
    simpa [prefixWord, tailWord_2110213, baseEnd_2110213] using wordTrace_append hprefix tailTrace_2110213
  have hstable : (prefixWord ++ tailWord_2110213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110213).length < 2 ^ (prefixWord ++ tailWord_2110213).sum := by decide
  have hdescent : baseEnd_2110213 < baseStart_2110213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110280 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_2110280 : Nat := 118140960795 + 2110280 * 2 ^ 59
def prefixEnd_2110280 : Nat := 4983230072969 + 3 ^ 40 * 2110280 * 2
def baseEnd_2110280 : Nat := 1083587955570108753495005

theorem tailTrace_2110280 : CollatzResearch.WordTrace tailWord_2110280 prefixEnd_2110280 1083587955570108753495005 := by
  unfold tailWord_2110280
  simp only [CollatzResearch.WordTrace]
  refine ⟨38484117397411720987816147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51312156529882294650421529 38484117397411720987816147)
  ·
    refine ⟨57726176096117581481724221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38484117397411720987816147 57726176096117581481724221)
    ·
      refine ⟨21647316036044093055646583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57726176096117581481724221 21647316036044093055646583)
      ·
        refine ⟨32470974054066139583469875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21647316036044093055646583 32470974054066139583469875)
        ·
          refine ⟨48706461081099209375204813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32470974054066139583469875 48706461081099209375204813)
          ·
            refine ⟨18264922905412203515701805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48706461081099209375204813 18264922905412203515701805)
            ·
              refine ⟨6849346089529576318388177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18264922905412203515701805 6849346089529576318388177)
              ·
                refine ⟨5137009567147182238791133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6849346089529576318388177 5137009567147182238791133)
                ·
                  refine ⟨1926378587680193339546675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5137009567147182238791133 1926378587680193339546675)
                  ·
                    refine ⟨2889567881520290009320013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926378587680193339546675 2889567881520290009320013)
                    ·
                      refine ⟨1083587955570108753495005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889567881520290009320013 1083587955570108753495005)
                      ·
                        rfl

theorem cell23_2110280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_2110280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110280 prefixEnd_2110280 := by exact prefixLift 2110280
  have htrace : WordTrace (prefixWord ++ tailWord_2110280) baseStart_2110280 baseEnd_2110280 := by
    simpa [prefixWord, tailWord_2110280, baseEnd_2110280] using wordTrace_append hprefix tailTrace_2110280
  have hstable : (prefixWord ++ tailWord_2110280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110280).length < 2 ^ (prefixWord ++ tailWord_2110280).sum := by decide
  have hdescent : baseEnd_2110280 < baseStart_2110280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110290 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_2110290 : Nat := 118140960795 + 2110290 * 2 ^ 59
def prefixEnd_2110290 : Nat := 4983230072969 + 3 ^ 40 * 2110290 * 2
def baseEnd_2110290 : Nat := 1083593090376653714369959

theorem tailTrace_2110290 : CollatzResearch.WordTrace tailWord_2110290 prefixEnd_2110290 1083593090376653714369959 := by
  unfold tailWord_2110290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19242149881196803420874081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51312399683191475788997549 19242149881196803420874081)
  ·
    refine ⟨14431612410897602565655561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19242149881196803420874081 14431612410897602565655561)
    ·
      refine ⟨10823709308173201924241671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14431612410897602565655561 10823709308173201924241671)
      ·
        refine ⟨16235563962259802886362507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10823709308173201924241671 16235563962259802886362507)
        ·
          refine ⟨24353345943389704329543761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16235563962259802886362507 24353345943389704329543761)
          ·
            refine ⟨18265009457542278247157821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24353345943389704329543761 18265009457542278247157821)
            ·
              refine ⟨6849378546578354342684183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18265009457542278247157821 6849378546578354342684183)
              ·
                refine ⟨10274067819867531514026275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6849378546578354342684183 10274067819867531514026275)
                ·
                  refine ⟨15411101729801297271039413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10274067819867531514026275 15411101729801297271039413)
                  ·
                    refine ⟨1444790787168871619159945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15411101729801297271039413 1444790787168871619159945)
                    ·
                      refine ⟨1083593090376653714369959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444790787168871619159945 1083593090376653714369959)
                      ·
                        rfl

theorem cell23_2110290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_2110290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110290 prefixEnd_2110290 := by exact prefixLift 2110290
  have htrace : WordTrace (prefixWord ++ tailWord_2110290) baseStart_2110290 baseEnd_2110290 := by
    simpa [prefixWord, tailWord_2110290, baseEnd_2110290] using wordTrace_append hprefix tailTrace_2110290
  have hstable : (prefixWord ++ tailWord_2110290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110290).length < 2 ^ (prefixWord ++ tailWord_2110290).sum := by decide
  have hdescent : baseEnd_2110290 < baseStart_2110290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110297 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 1, 1, 3]
def baseStart_2110297 : Nat := 118140960795 + 2110297 * 2 ^ 59
def prefixEnd_2110297 : Nat := 4983230072969 + 3 ^ 40 * 2110297 * 2
def baseEnd_2110297 : Nat := 1083596684741235186982427

theorem tailTrace_2110297 : CollatzResearch.WordTrace tailWord_2110297 prefixEnd_2110297 1083596684741235186982427 := by
  unfold tailWord_2110297
  simp only [CollatzResearch.WordTrace]
  refine ⟨76968854835761853879001145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51312569890507902586000763 76968854835761853879001145)
  ·
    refine ⟨57726641126821390409250859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76968854835761853879001145 57726641126821390409250859)
    ·
      refine ⟨86589961690232085613876289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57726641126821390409250859 86589961690232085613876289)
      ·
        refine ⟨64942471267674064210407217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86589961690232085613876289 64942471267674064210407217)
        ·
          refine ⟨48706853450755548157805413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64942471267674064210407217 48706853450755548157805413)
          ·
            refine ⟨9132535022016665279588515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48706853450755548157805413 9132535022016665279588515)
            ·
              refine ⟨13698802533024997919382773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9132535022016665279588515 13698802533024997919382773)
              ·
                refine ⟨1284262737471093554942135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13698802533024997919382773 1284262737471093554942135)
                ·
                  refine ⟨1926394106206640332413203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284262737471093554942135 1926394106206640332413203)
                  ·
                    refine ⟨2889591159309960498619805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926394106206640332413203 2889591159309960498619805)
                    ·
                      refine ⟨1083596684741235186982427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889591159309960498619805 1083596684741235186982427)
                      ·
                        rfl

theorem cell23_2110297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_2110297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110297 prefixEnd_2110297 := by exact prefixLift 2110297
  have htrace : WordTrace (prefixWord ++ tailWord_2110297) baseStart_2110297 baseEnd_2110297 := by
    simpa [prefixWord, tailWord_2110297, baseEnd_2110297] using wordTrace_append hprefix tailTrace_2110297
  have hstable : (prefixWord ++ tailWord_2110297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110297).length < 2 ^ (prefixWord ++ tailWord_2110297).sum := by decide
  have hdescent : baseEnd_2110297 < baseStart_2110297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110323 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3]
def baseStart_2110323 : Nat := 118140960795 + 2110323 * 2 ^ 59
def prefixEnd_2110323 : Nat := 4983230072969 + 3 ^ 40 * 2110323 * 2
def baseEnd_2110323 : Nat := 1083610035238252085257307

theorem tailTrace_2110323 : CollatzResearch.WordTrace tailWord_2110323 prefixEnd_2110323 1083610035238252085257307 := by
  unfold tailWord_2110323
  simp only [CollatzResearch.WordTrace]
  refine ⟨76969803133667660319447623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51313202089111773546298415 76969803133667660319447623)
  ·
    refine ⟨115454704700501490479171435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76969803133667660319447623 115454704700501490479171435)
    ·
      refine ⟨173182057050752235718757153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115454704700501490479171435 173182057050752235718757153)
      ·
        refine ⟨129886542788064176789067865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173182057050752235718757153 129886542788064176789067865)
        ·
          refine ⟨97414907091048132591800899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129886542788064176789067865 97414907091048132591800899)
          ·
            refine ⟨146122360636572198887701349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97414907091048132591800899 146122360636572198887701349)
            ·
              refine ⟨27397942619357287291444003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146122360636572198887701349 27397942619357287291444003)
              ·
                refine ⟨41096913929035930937166005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27397942619357287291444003 41096913929035930937166005)
                ·
                  refine ⟨3852835680847118525359313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41096913929035930937166005 3852835680847118525359313)
                  ·
                    refine ⟨2889626760635338894019485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3852835680847118525359313 2889626760635338894019485)
                    ·
                      refine ⟨1083610035238252085257307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889626760635338894019485 1083610035238252085257307)
                      ·
                        rfl

theorem cell23_2110323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_2110323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110323 prefixEnd_2110323 := by exact prefixLift 2110323
  have htrace : WordTrace (prefixWord ++ tailWord_2110323) baseStart_2110323 baseEnd_2110323 := by
    simpa [prefixWord, tailWord_2110323, baseEnd_2110323] using wordTrace_append hprefix tailTrace_2110323
  have hstable : (prefixWord ++ tailWord_2110323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110323).length < 2 ^ (prefixWord ++ tailWord_2110323).sum := by decide
  have hdescent : baseEnd_2110323 < baseStart_2110323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110334 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2110334 : Nat := 118140960795 + 2110334 * 2 ^ 59
def prefixEnd_2110334 : Nat := 4983230072969 + 3 ^ 40 * 2110334 * 2
def baseEnd_2110334 : Nat := 361205227841817180739919

theorem tailTrace_2110334 : CollatzResearch.WordTrace tailWord_2110334 prefixEnd_2110334 361205227841817180739919 := by
  unfold tailWord_2110334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621275542078476149762257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51313469557751872798732037 9621275542078476149762257)
  ·
    refine ⟨7215956656558857112321693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9621275542078476149762257 7215956656558857112321693)
    ·
      refine ⟨2705983746209571417120635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7215956656558857112321693 2705983746209571417120635)
      ·
        refine ⟨4058975619314357125680953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2705983746209571417120635 4058975619314357125680953)
        ·
          refine ⟨3044231714485767844260715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4058975619314357125680953 3044231714485767844260715)
          ·
            refine ⟨4566347571728651766391073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044231714485767844260715 4566347571728651766391073)
            ·
              refine ⟨3424760678796488824793305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566347571728651766391073 3424760678796488824793305)
              ·
                refine ⟨2568570509097366618594979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3424760678796488824793305 2568570509097366618594979)
                ·
                  refine ⟨3852855763646049927892469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568570509097366618594979 3852855763646049927892469)
                  ·
                    refine ⟨361205227841817180739919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3852855763646049927892469 361205227841817180739919)
                    ·
                      rfl

theorem cell23_2110334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2110334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110334 prefixEnd_2110334 := by exact prefixLift 2110334
  have htrace : WordTrace (prefixWord ++ tailWord_2110334) baseStart_2110334 baseEnd_2110334 := by
    simpa [prefixWord, tailWord_2110334, baseEnd_2110334] using wordTrace_append hprefix tailTrace_2110334
  have hstable : (prefixWord ++ tailWord_2110334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110334).length < 2 ^ (prefixWord ++ tailWord_2110334).sum := by decide
  have hdescent : baseEnd_2110334 < baseStart_2110334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110343 : List Nat := [1, 1, 4, 2, 3, 2, 1, 9]
def baseStart_2110343 : Nat := 118140960795 + 2110343 * 2 ^ 59
def prefixEnd_2110343 : Nat := 4983230072969 + 3 ^ 40 * 2110343 * 2
def baseEnd_2110343 : Nat := 40134085364864518778045

theorem tailTrace_2110343 : CollatzResearch.WordTrace tailWord_2110343 prefixEnd_2110343 40134085364864518778045 := by
  unfold tailWord_2110343
  simp only [CollatzResearch.WordTrace]
  refine ⟨76970532593595203735175683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51313688395730135823450455 76970532593595203735175683)
  ·
    refine ⟨115455798890392805602763525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76970532593595203735175683 115455798890392805602763525)
    ·
      refine ⟨21647962291948651050518161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115455798890392805602763525 21647962291948651050518161)
      ·
        refine ⟨16235971718961488287888621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21647962291948651050518161 16235971718961488287888621)
        ·
          refine ⟨6088489394610558107958233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16235971718961488287888621 6088489394610558107958233)
          ·
            refine ⟨4566367045957918580968675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6088489394610558107958233 4566367045957918580968675)
            ·
              refine ⟨6849550568936877871453013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566367045957918580968675 6849550568936877871453013)
              ·
                refine ⟨40134085364864518778045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6849550568936877871453013 40134085364864518778045)
                ·
                  rfl

theorem cell23_2110343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 9].length) (baseStart_2110343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110343 prefixEnd_2110343 := by exact prefixLift 2110343
  have htrace : WordTrace (prefixWord ++ tailWord_2110343) baseStart_2110343 baseEnd_2110343 := by
    simpa [prefixWord, tailWord_2110343, baseEnd_2110343] using wordTrace_append hprefix tailTrace_2110343
  have hstable : (prefixWord ++ tailWord_2110343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110343).length < 2 ^ (prefixWord ++ tailWord_2110343).sum := by decide
  have hdescent : baseEnd_2110343 < baseStart_2110343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110353 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_2110353 : Nat := 118140960795 + 2110353 * 2 ^ 59
def prefixEnd_2110353 : Nat := 4983230072969 + 3 ^ 40 * 2110353 * 2
def baseEnd_2110353 : Nat := 1083625439657886967882169

theorem tailTrace_2110353 : CollatzResearch.WordTrace tailWord_2110353 prefixEnd_2110353 1083625439657886967882169 := by
  unfold tailWord_2110353
  simp only [CollatzResearch.WordTrace]
  refine ⟨76970897323558975443039713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51313931549039316962026475 76970897323558975443039713)
  ·
    refine ⟨57728172992669231582279785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76970897323558975443039713 57728172992669231582279785)
    ·
      refine ⟨43296129744501923686709839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57728172992669231582279785 43296129744501923686709839)
      ·
        refine ⟨64944194616752885530064759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43296129744501923686709839 64944194616752885530064759)
        ·
          refine ⟨97416291925129328295097139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64944194616752885530064759 97416291925129328295097139)
          ·
            refine ⟨146124437887693992442645709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97416291925129328295097139 146124437887693992442645709)
            ·
              refine ⟨54796664207885247165992141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146124437887693992442645709 54796664207885247165992141)
              ·
                refine ⟨20548749077956967687247053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54796664207885247165992141 20548749077956967687247053)
                ·
                  refine ⟨7705780904233862882717645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20548749077956967687247053 7705780904233862882717645)
                  ·
                    refine ⟨2889667839087698581019117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7705780904233862882717645 2889667839087698581019117)
                    ·
                      refine ⟨1083625439657886967882169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889667839087698581019117 1083625439657886967882169)
                      ·
                        rfl

theorem cell23_2110353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_2110353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110353 prefixEnd_2110353 := by exact prefixLift 2110353
  have htrace : WordTrace (prefixWord ++ tailWord_2110353) baseStart_2110353 baseEnd_2110353 := by
    simpa [prefixWord, tailWord_2110353, baseEnd_2110353] using wordTrace_append hprefix tailTrace_2110353
  have hstable : (prefixWord ++ tailWord_2110353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110353).length < 2 ^ (prefixWord ++ tailWord_2110353).sum := by decide
  have hdescent : baseEnd_2110353 < baseStart_2110353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110380 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_2110380 : Nat := 118140960795 + 2110380 * 2 ^ 59
def prefixEnd_2110380 : Nat := 4983230072969 + 3 ^ 40 * 2110380 * 2
def baseEnd_2110380 : Nat := 1083639303635558362244545

theorem tailTrace_2110380 : CollatzResearch.WordTrace tailWord_2110380 prefixEnd_2110380 1083639303635558362244545 := by
  unfold tailWord_2110380
  simp only [CollatzResearch.WordTrace]
  refine ⟨38485941047230579527136297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51314588062974106036181729 38485941047230579527136297)
  ·
    refine ⟨28864455785422934645352223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38485941047230579527136297 28864455785422934645352223)
    ·
      refine ⟨43296683678134401968028335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28864455785422934645352223 43296683678134401968028335)
      ·
        refine ⟨64945025517201602952042503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43296683678134401968028335 64945025517201602952042503)
        ·
          refine ⟨97417538275802404428063755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64945025517201602952042503 97417538275802404428063755)
          ·
            refine ⟨146126307413703606642095633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97417538275802404428063755 146126307413703606642095633)
            ·
              refine ⟨109594730560277704981571725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146126307413703606642095633 109594730560277704981571725)
              ·
                refine ⟨41098023960104139368089397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109594730560277704981571725 41098023960104139368089397)
                ·
                  refine ⟨3852939746259763065758381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41098023960104139368089397 3852939746259763065758381)
                  ·
                    refine ⟨1444852404847411149659393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3852939746259763065758381 1444852404847411149659393)
                    ·
                      refine ⟨1083639303635558362244545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1444852404847411149659393 1083639303635558362244545)
                      ·
                        rfl

theorem cell23_2110380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_2110380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110380 prefixEnd_2110380 := by exact prefixLift 2110380
  have htrace : WordTrace (prefixWord ++ tailWord_2110380) baseStart_2110380 baseEnd_2110380 := by
    simpa [prefixWord, tailWord_2110380, baseEnd_2110380] using wordTrace_append hprefix tailTrace_2110380
  have hstable : (prefixWord ++ tailWord_2110380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110380).length < 2 ^ (prefixWord ++ tailWord_2110380).sum := by decide
  have hdescent : baseEnd_2110380 < baseStart_2110380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110404 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2110404 : Nat := 118140960795 + 2110404 * 2 ^ 59
def prefixEnd_2110404 : Nat := 4983230072969 + 3 ^ 40 * 2110404 * 2
def baseEnd_2110404 : Nat := 1083651627171266268344435

theorem tailTrace_2110404 : CollatzResearch.WordTrace tailWord_2110404 prefixEnd_2110404 1083651627171266268344435 := by
  unfold tailWord_2110404
  simp only [CollatzResearch.WordTrace]
  refine ⟨38486378723187105576573133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51315171630916140768764177 38486378723187105576573133)
  ·
    refine ⟨14432392021195164591214925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38486378723187105576573133 14432392021195164591214925)
    ·
      refine ⟨5412147007948186721705597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14432392021195164591214925 5412147007948186721705597)
      ·
        refine ⟨2029555127980570020639599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5412147007948186721705597 2029555127980570020639599)
        ·
          refine ⟨3044332691970855030959399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029555127980570020639599 3044332691970855030959399)
          ·
            refine ⟨4566499037956282546439099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044332691970855030959399 4566499037956282546439099)
            ·
              refine ⟨6849748556934423819658649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566499037956282546439099 6849748556934423819658649)
              ·
                refine ⟨5137311417700817864743987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6849748556934423819658649 5137311417700817864743987)
                ·
                  refine ⟨7705967126551226797115981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137311417700817864743987 7705967126551226797115981)
                  ·
                    refine ⟨2889737672456710048918493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7705967126551226797115981 2889737672456710048918493)
                    ·
                      refine ⟨1083651627171266268344435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2889737672456710048918493 1083651627171266268344435)
                      ·
                        rfl

theorem cell23_2110404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2110404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110404 prefixEnd_2110404 := by exact prefixLift 2110404
  have htrace : WordTrace (prefixWord ++ tailWord_2110404) baseStart_2110404 baseEnd_2110404 := by
    simpa [prefixWord, tailWord_2110404, baseEnd_2110404] using wordTrace_append hprefix tailTrace_2110404
  have hstable : (prefixWord ++ tailWord_2110404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110404).length < 2 ^ (prefixWord ++ tailWord_2110404).sum := by decide
  have hdescent : baseEnd_2110404 < baseStart_2110404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110433 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 7]
def baseStart_2110433 : Nat := 118140960795 + 2110433 * 2 ^ 59
def prefixEnd_2110433 : Nat := 4983230072969 + 3 ^ 40 * 2110433 * 2
def baseEnd_2110433 : Nat := 120407390901138517209089

theorem tailTrace_2110433 : CollatzResearch.WordTrace tailWord_2110433 prefixEnd_2110433 120407390901138517209089 := by
  unfold tailWord_2110433
  simp only [CollatzResearch.WordTrace]
  refine ⟨76973815163269149105951953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51315876775512766070634635 76973815163269149105951953)
  ·
    refine ⟨57730361372451861829463965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76973815163269149105951953 57730361372451861829463965)
    ·
      refine ⟨21648885514669448186048987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57730361372451861829463965 21648885514669448186048987)
      ·
        refine ⟨32473328272004172279073481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21648885514669448186048987 32473328272004172279073481)
        ·
          refine ⟨24354996204003129209305111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32473328272004172279073481 24354996204003129209305111)
          ·
            refine ⟨36532494306004693813957667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24354996204003129209305111 36532494306004693813957667)
            ·
              refine ⟨54798741459007040720936501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36532494306004693813957667 54798741459007040720936501)
              ·
                refine ⟨5137382011781910067587797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54798741459007040720936501 5137382011781910067587797)
                ·
                  refine ⟨120407390901138517209089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5137382011781910067587797 120407390901138517209089)
                  ·
                    rfl

theorem cell23_2110433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_2110433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110433 prefixEnd_2110433 := by exact prefixLift 2110433
  have htrace : WordTrace (prefixWord ++ tailWord_2110433) baseStart_2110433 baseEnd_2110433 := by
    simpa [prefixWord, tailWord_2110433, baseEnd_2110433] using wordTrace_append hprefix tailTrace_2110433
  have hstable : (prefixWord ++ tailWord_2110433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110433).length < 2 ^ (prefixWord ++ tailWord_2110433).sum := by decide
  have hdescent : baseEnd_2110433 < baseStart_2110433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110437 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_2110437 : Nat := 118140960795 + 2110437 * 2 ^ 59
def prefixEnd_2110437 : Nat := 4983230072969 + 3 ^ 40 * 2110437 * 2
def baseEnd_2110437 : Nat := 361222857344288213077261

theorem tailTrace_2110437 : CollatzResearch.WordTrace tailWord_2110437 prefixEnd_2110437 361222857344288213077261 := by
  unfold tailWord_2110437
  simp only [CollatzResearch.WordTrace]
  refine ⟨76973961055254657789097565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51315974036836438526065043 76973961055254657789097565)
  ·
    refine ⟨28865235395720496670911587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76973961055254657789097565 28865235395720496670911587)
    ·
      refine ⟨43297853093580745006367381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28865235395720496670911587 43297853093580745006367381)
      ·
        refine ⟨2029586863761597422173471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43297853093580745006367381 2029586863761597422173471)
        ·
          refine ⟨3044380295642396133260207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029586863761597422173471 3044380295642396133260207)
          ·
            refine ⟨4566570443463594199890311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044380295642396133260207 4566570443463594199890311)
            ·
              refine ⟨6849855665195391299835467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566570443463594199890311 6849855665195391299835467)
              ·
                refine ⟨10274783497793086949753201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6849855665195391299835467 10274783497793086949753201)
                ·
                  refine ⟨7706087623344815212314901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10274783497793086949753201 7706087623344815212314901)
                  ·
                    refine ⟨361222857344288213077261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7706087623344815212314901 361222857344288213077261)
                    ·
                      rfl

theorem cell23_2110437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_2110437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110437 prefixEnd_2110437 := by exact prefixLift 2110437
  have htrace : WordTrace (prefixWord ++ tailWord_2110437) baseStart_2110437 baseEnd_2110437 := by
    simpa [prefixWord, tailWord_2110437, baseEnd_2110437] using wordTrace_append hprefix tailTrace_2110437
  have hstable : (prefixWord ++ tailWord_2110437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110437).length < 2 ^ (prefixWord ++ tailWord_2110437).sum := by decide
  have hdescent : baseEnd_2110437 < baseStart_2110437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110473 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_2110473 : Nat := 118140960795 + 2110473 * 2 ^ 59
def prefixEnd_2110473 : Nat := 4983230072969 + 3 ^ 40 * 2110473 * 2
def baseEnd_2110473 : Nat := 1083687057336426498381617

theorem tailTrace_2110473 : CollatzResearch.WordTrace tailWord_2110473 prefixEnd_2110473 1083687057336426498381617 := by
  unfold tailWord_2110473
  simp only [CollatzResearch.WordTrace]
  refine ⟨76975274083124235937408073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51316849388749490624938715 76975274083124235937408073)
  ·
    refine ⟨57731455562343176953056055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76975274083124235937408073 57731455562343176953056055)
    ·
      refine ⟨86597183343514765429584083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57731455562343176953056055 86597183343514765429584083)
      ·
        refine ⟨129895775015272148144376125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86597183343514765429584083 129895775015272148144376125)
        ·
          refine ⟨48710915630727055554141047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129895775015272148144376125 48710915630727055554141047)
          ·
            refine ⟨73066373446090583331211571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48710915630727055554141047 73066373446090583331211571)
            ·
              refine ⟨109599560169135874996817357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73066373446090583331211571 109599560169135874996817357)
              ·
                refine ⟨41099835063425953123806509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109599560169135874996817357 41099835063425953123806509)
                ·
                  refine ⟨15412438148784732421427441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41099835063425953123806509 15412438148784732421427441)
                  ·
                    refine ⟨11559328611588549316070581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15412438148784732421427441 11559328611588549316070581)
                    ·
                      refine ⟨1083687057336426498381617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11559328611588549316070581 1083687057336426498381617)
                      ·
                        rfl

theorem cell23_2110473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_2110473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110473 prefixEnd_2110473 := by exact prefixLift 2110473
  have htrace : WordTrace (prefixWord ++ tailWord_2110473) baseStart_2110473 baseEnd_2110473 := by
    simpa [prefixWord, tailWord_2110473, baseEnd_2110473] using wordTrace_append hprefix tailTrace_2110473
  have hstable : (prefixWord ++ tailWord_2110473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110473).length < 2 ^ (prefixWord ++ tailWord_2110473).sum := by decide
  have hdescent : baseEnd_2110473 < baseStart_2110473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110510 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2110510 : Nat := 118140960795 + 2110510 * 2 ^ 59
def prefixEnd_2110510 : Nat := 4983230072969 + 3 ^ 40 * 2110510 * 2
def baseEnd_2110510 : Nat := 361235352040214284539649

theorem tailTrace_2110510 : CollatzResearch.WordTrace tailWord_2110510 prefixEnd_2110510 361235352040214284539649 := by
  unfold tailWord_2110510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9622077947998773907063123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51317749055993460837669989 9622077947998773907063123)
  ·
    refine ⟨14433116921998160860594685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9622077947998773907063123 14433116921998160860594685)
    ·
      refine ⟨5412418845749310322723007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14433116921998160860594685 5412418845749310322723007)
      ·
        refine ⟨8118628268623965484084511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412418845749310322723007 8118628268623965484084511)
        ·
          refine ⟨12177942402935948226126767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118628268623965484084511 12177942402935948226126767)
          ·
            refine ⟨18266913604403922339190151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12177942402935948226126767 18266913604403922339190151)
            ·
              refine ⟨27400370406605883508785227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18266913604403922339190151 27400370406605883508785227)
              ·
                refine ⟨41100555609908825263177841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27400370406605883508785227 41100555609908825263177841)
                ·
                  refine ⟨30825416707431618947383381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41100555609908825263177841 30825416707431618947383381)
                  ·
                    refine ⟨361235352040214284539649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30825416707431618947383381 361235352040214284539649)
                    ·
                      rfl

theorem cell23_2110510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2110510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110510 prefixEnd_2110510 := by exact prefixLift 2110510
  have htrace : WordTrace (prefixWord ++ tailWord_2110510) baseStart_2110510 baseEnd_2110510 := by
    simpa [prefixWord, tailWord_2110510, baseEnd_2110510] using wordTrace_append hprefix tailTrace_2110510
  have hstable : (prefixWord ++ tailWord_2110510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110510).length < 2 ^ (prefixWord ++ tailWord_2110510).sum := by decide
  have hdescent : baseEnd_2110510 < baseStart_2110510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110534 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2110534 : Nat := 118140960795 + 2110534 * 2 ^ 59
def prefixEnd_2110534 : Nat := 4983230072969 + 3 ^ 40 * 2110534 * 2
def baseEnd_2110534 : Nat := 1083718379656350759718837

theorem tailTrace_2110534 : CollatzResearch.WordTrace tailWord_2110534 prefixEnd_2110534 1083718379656350759718837 := by
  unfold tailWord_2110534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405546841746976354855583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51318332623935495570252437 2405546841746976354855583)
  ·
    refine ⟨3608320262620464532283375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2405546841746976354855583 3608320262620464532283375)
    ·
      refine ⟨5412480393930696798425063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608320262620464532283375 5412480393930696798425063)
      ·
        refine ⟨8118720590896045197637595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412480393930696798425063 8118720590896045197637595)
        ·
          refine ⟨12178080886344067796456393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118720590896045197637595 12178080886344067796456393)
          ·
            refine ⟨9133560664758050847342295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12178080886344067796456393 9133560664758050847342295)
            ·
              refine ⟨13700340997137076271013443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9133560664758050847342295 13700340997137076271013443)
              ·
                refine ⟨20550511495705614406520165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13700340997137076271013443 20550511495705614406520165)
                ·
                  refine ⟨3853220905444802701222531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20550511495705614406520165 3853220905444802701222531)
                  ·
                    refine ⟨5779831358167204051833797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853220905444802701222531 5779831358167204051833797)
                    ·
                      refine ⟨1083718379656350759718837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5779831358167204051833797 1083718379656350759718837)
                      ·
                        rfl

theorem cell23_2110534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2110534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110534 prefixEnd_2110534 := by exact prefixLift 2110534
  have htrace : WordTrace (prefixWord ++ tailWord_2110534) baseStart_2110534 baseEnd_2110534 := by
    simpa [prefixWord, tailWord_2110534, baseEnd_2110534] using wordTrace_append hprefix tailTrace_2110534
  have hstable : (prefixWord ++ tailWord_2110534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110534).length < 2 ^ (prefixWord ++ tailWord_2110534).sum := by decide
  have hdescent : baseEnd_2110534 < baseStart_2110534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110540 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 6]
def baseStart_2110540 : Nat := 118140960795 + 2110540 * 2 ^ 59
def prefixEnd_2110540 : Nat := 4983230072969 + 3 ^ 40 * 2110540 * 2
def baseEnd_2110540 : Nat := 120413495615586415138201

theorem tailTrace_2110540 : CollatzResearch.WordTrace tailWord_2110540 prefixEnd_2110540 120413495615586415138201 := by
  unfold tailWord_2110540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38488858886940753190048537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51318478515921004253398049 38488858886940753190048537)
  ·
    refine ⟨28866644165205564892536403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38488858886940753190048537 28866644165205564892536403)
    ·
      refine ⟨43299966247808347338804605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28866644165205564892536403 43299966247808347338804605)
      ·
        refine ⟨16237487342928130252051727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43299966247808347338804605 16237487342928130252051727)
        ·
          refine ⟨24356231014392195378077591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16237487342928130252051727 24356231014392195378077591)
          ·
            refine ⟨36534346521588293067116387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24356231014392195378077591 36534346521588293067116387)
            ·
              refine ⟨54801519782382439600674581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36534346521588293067116387 54801519782382439600674581)
              ·
                refine ⟨2568821239799176856281621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54801519782382439600674581 2568821239799176856281621)
                ·
                  refine ⟨120413495615586415138201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2568821239799176856281621 120413495615586415138201)
                  ·
                    rfl

theorem cell23_2110540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_2110540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110540 prefixEnd_2110540 := by exact prefixLift 2110540
  have htrace : WordTrace (prefixWord ++ tailWord_2110540) baseStart_2110540 baseEnd_2110540 := by
    simpa [prefixWord, tailWord_2110540, baseEnd_2110540] using wordTrace_append hprefix tailTrace_2110540
  have hstable : (prefixWord ++ tailWord_2110540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110540).length < 2 ^ (prefixWord ++ tailWord_2110540).sum := by decide
  have hdescent : baseEnd_2110540 < baseStart_2110540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110601 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 1, 1, 3]
def baseStart_2110601 : Nat := 118140960795 + 2110601 * 2 ^ 59
def prefixEnd_2110601 : Nat := 4983230072969 + 3 ^ 40 * 2110601 * 2
def baseEnd_2110601 : Nat := 1083752782860201997581029

theorem tailTrace_2110601 : CollatzResearch.WordTrace tailWord_2110601 prefixEnd_2110601 1083752782860201997581029 := by
  unfold tailWord_2110601
  simp only [CollatzResearch.WordTrace]
  refine ⟨76979942626660513798067657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51319961751107009198711771 76979942626660513798067657)
  ·
    refine ⟨57734956969995385348550743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76979942626660513798067657 57734956969995385348550743)
    ·
      refine ⟨86602435454993078022826115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57734956969995385348550743 86602435454993078022826115)
      ·
        refine ⟨129903653182489617034239173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86602435454993078022826115 129903653182489617034239173)
        ·
          refine ⟨24356934971716803193919845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129903653182489617034239173 24356934971716803193919845)
          ·
            refine ⟨4566925307196900598859971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24356934971716803193919845 4566925307196900598859971)
            ·
              refine ⟨6850387960795350898289957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566925307196900598859971 6850387960795350898289957)
              ·
                refine ⟨1284447742649128293429367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6850387960795350898289957 1284447742649128293429367)
                ·
                  refine ⟨1926671613973692440144051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284447742649128293429367 1926671613973692440144051)
                  ·
                    refine ⟨2890007420960538660216077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1926671613973692440144051 2890007420960538660216077)
                    ·
                      refine ⟨1083752782860201997581029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890007420960538660216077 1083752782860201997581029)
                      ·
                        rfl

theorem cell23_2110601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 1, 3].length) (baseStart_2110601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110601 prefixEnd_2110601 := by exact prefixLift 2110601
  have htrace : WordTrace (prefixWord ++ tailWord_2110601) baseStart_2110601 baseEnd_2110601 := by
    simpa [prefixWord, tailWord_2110601, baseEnd_2110601] using wordTrace_append hprefix tailTrace_2110601
  have hstable : (prefixWord ++ tailWord_2110601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110601).length < 2 ^ (prefixWord ++ tailWord_2110601).sum := by decide
  have hdescent : baseEnd_2110601 < baseStart_2110601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110634 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2110634 : Nat := 118140960795 + 2110634 * 2 ^ 59
def prefixEnd_2110634 : Nat := 4983230072969 + 3 ^ 40 * 2110634 * 2
def baseEnd_2110634 : Nat := 361256575907266789489459

theorem tailTrace_2110634 : CollatzResearch.WordTrace tailWord_2110634 prefixEnd_2110634 361256575907266789489459 := by
  unfold tailWord_2110634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19245286558885240108504739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51320764157027306956012637 19245286558885240108504739)
  ·
    refine ⟨28867929838327860162757109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19245286558885240108504739 28867929838327860162757109)
    ·
      refine ⟨2706368422343236890258479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28867929838327860162757109 2706368422343236890258479)
      ·
        refine ⟨4059552633514855335387719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706368422343236890258479 4059552633514855335387719)
        ·
          refine ⟨6089328950272283003081579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059552633514855335387719 6089328950272283003081579)
          ·
            refine ⟨9133993425408424504622369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089328950272283003081579 9133993425408424504622369)
            ·
              refine ⟨6850495069056318378466777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9133993425408424504622369 6850495069056318378466777)
              ·
                refine ⟨5137871301792238783850083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6850495069056318378466777 5137871301792238783850083)
                ·
                  refine ⟨7706806952688358175775125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137871301792238783850083 7706806952688358175775125)
                  ·
                    refine ⟨361256575907266789489459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7706806952688358175775125 361256575907266789489459)
                    ·
                      rfl

theorem cell23_2110634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2110634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110634 prefixEnd_2110634 := by exact prefixLift 2110634
  have htrace : WordTrace (prefixWord ++ tailWord_2110634) baseStart_2110634 baseEnd_2110634 := by
    simpa [prefixWord, tailWord_2110634, baseEnd_2110634] using wordTrace_append hprefix tailTrace_2110634
  have hstable : (prefixWord ++ tailWord_2110634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110634).length < 2 ^ (prefixWord ++ tailWord_2110634).sum := by decide
  have hdescent : baseEnd_2110634 < baseStart_2110634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110641 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2110641 : Nat := 118140960795 + 2110641 * 2 ^ 59
def prefixEnd_2110641 : Nat := 4983230072969 + 3 ^ 40 * 2110641 * 2
def baseEnd_2110641 : Nat := 1083773322086381841080845

theorem tailTrace_2110641 : CollatzResearch.WordTrace tailWord_2110641 prefixEnd_2110641 1083773322086381841080845 := by
  unfold tailWord_2110641
  simp only [CollatzResearch.WordTrace]
  refine ⟨76981401546515600629523777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51320934364343733753015851 76981401546515600629523777)
  ·
    refine ⟨57736051159886700472142833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76981401546515600629523777 57736051159886700472142833)
    ·
      refine ⟨43302038369915025354107125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57736051159886700472142833 43302038369915025354107125)
      ·
        refine ⟨4059566097179533626947543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43302038369915025354107125 4059566097179533626947543)
        ·
          refine ⟨6089349145769300440421315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059566097179533626947543 6089349145769300440421315)
          ·
            refine ⟨9134023718653950660631973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089349145769300440421315 9134023718653950660631973)
            ·
              refine ⟨1712629447247615748868495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9134023718653950660631973 1712629447247615748868495)
              ·
                refine ⟨2568944170871423623302743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712629447247615748868495 2568944170871423623302743)
                ·
                  refine ⟨3853416256307135434954115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568944170871423623302743 3853416256307135434954115)
                  ·
                    refine ⟨5780124384460703152431173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3853416256307135434954115 5780124384460703152431173)
                    ·
                      refine ⟨1083773322086381841080845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5780124384460703152431173 1083773322086381841080845)
                      ·
                        rfl

theorem cell23_2110641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2110641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110641 prefixEnd_2110641 := by exact prefixLift 2110641
  have htrace : WordTrace (prefixWord ++ tailWord_2110641) baseStart_2110641 baseEnd_2110641 := by
    simpa [prefixWord, tailWord_2110641, baseEnd_2110641] using wordTrace_append hprefix tailTrace_2110641
  have hstable : (prefixWord ++ tailWord_2110641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110641).length < 2 ^ (prefixWord ++ tailWord_2110641).sum := by decide
  have hdescent : baseEnd_2110641 < baseStart_2110641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110650 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_2110650 : Nat := 118140960795 + 2110650 * 2 ^ 59
def prefixEnd_2110650 : Nat := 4983230072969 + 3 ^ 40 * 2110650 * 2
def baseEnd_2110650 : Nat := 1083777943412272305868303

theorem tailTrace_2110650 : CollatzResearch.WordTrace tailWord_2110650 prefixEnd_2110650 1083777943412272305868303 := by
  unfold tailWord_2110650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19245432450870748791650351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51321153202321996777734269 19245432450870748791650351)
  ·
    refine ⟨28868148676306123187475527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19245432450870748791650351 28868148676306123187475527)
    ·
      refine ⟨43302223014459184781213291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28868148676306123187475527 43302223014459184781213291)
      ·
        refine ⟨64953334521688777171819937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43302223014459184781213291 64953334521688777171819937)
        ·
          refine ⟨48715000891266582878864953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64953334521688777171819937 48715000891266582878864953)
          ·
            refine ⟨36536250668449937159148715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48715000891266582878864953 36536250668449937159148715)
            ·
              refine ⟨54804376002674905738723073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36536250668449937159148715 54804376002674905738723073)
              ·
                refine ⟨41103282002006179304042305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54804376002674905738723073 41103282002006179304042305)
                ·
                  refine ⟨30827461501504634478031729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41103282002006179304042305 30827461501504634478031729)
                  ·
                    refine ⟨23120596126128475858523797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30827461501504634478031729 23120596126128475858523797)
                    ·
                      refine ⟨1083777943412272305868303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23120596126128475858523797 1083777943412272305868303)
                      ·
                        rfl

theorem cell23_2110650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_2110650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110650 prefixEnd_2110650 := by exact prefixLift 2110650
  have htrace : WordTrace (prefixWord ++ tailWord_2110650) baseStart_2110650 baseEnd_2110650 := by
    simpa [prefixWord, tailWord_2110650, baseEnd_2110650] using wordTrace_append hprefix tailTrace_2110650
  have hstable : (prefixWord ++ tailWord_2110650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110650).length < 2 ^ (prefixWord ++ tailWord_2110650).sum := by decide
  have hdescent : baseEnd_2110650 < baseStart_2110650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110667 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 7, 2]
def baseStart_2110667 : Nat := 118140960795 + 2110667 * 2 ^ 59
def prefixEnd_2110667 : Nat := 4983230072969 + 3 ^ 40 * 2110667 * 2
def baseEnd_2110667 : Nat := 1083786672583398739355725

theorem tailTrace_2110667 : CollatzResearch.WordTrace tailWord_2110667 prefixEnd_2110667 1083786672583398739355725 := by
  unfold tailWord_2110667
  simp only [CollatzResearch.WordTrace]
  refine ⟨76982349844421407069970255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51321566562947604713313503 76982349844421407069970255)
  ·
    refine ⟨115473524766632110604955383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76982349844421407069970255 115473524766632110604955383)
    ·
      refine ⟨173210287149948165907433075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115473524766632110604955383 173210287149948165907433075)
      ·
        refine ⟨259815430724922248861149613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173210287149948165907433075 259815430724922248861149613)
        ·
          refine ⟨97430786521845843322931105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259815430724922248861149613 97430786521845843322931105)
          ·
            refine ⟨73073089891384382492198329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97430786521845843322931105 73073089891384382492198329)
            ·
              refine ⟨54804817418538286869148747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73073089891384382492198329 54804817418538286869148747)
              ·
                refine ⟨82207226127807430303723121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54804817418538286869148747 82207226127807430303723121)
                ·
                  refine ⟨61655419595855572727792341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82207226127807430303723121 61655419595855572727792341)
                  ·
                    refine ⟨1445048896777864985807633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61655419595855572727792341 1445048896777864985807633)
                    ·
                      refine ⟨1083786672583398739355725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445048896777864985807633 1083786672583398739355725)
                      ·
                        rfl

theorem cell23_2110667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7, 2].length) (baseStart_2110667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110667 prefixEnd_2110667 := by exact prefixLift 2110667
  have htrace : WordTrace (prefixWord ++ tailWord_2110667) baseStart_2110667 baseEnd_2110667 := by
    simpa [prefixWord, tailWord_2110667, baseEnd_2110667] using wordTrace_append hprefix tailTrace_2110667
  have hstable : (prefixWord ++ tailWord_2110667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110667).length < 2 ^ (prefixWord ++ tailWord_2110667).sum := by decide
  have hdescent : baseEnd_2110667 < baseStart_2110667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110747 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3]
def baseStart_2110747 : Nat := 118140960795 + 2110747 * 2 ^ 59
def prefixEnd_2110747 : Nat := 4983230072969 + 3 ^ 40 * 2110747 * 2
def baseEnd_2110747 : Nat := 1083827751035758426355357

theorem tailTrace_2110747 : CollatzResearch.WordTrace tailWord_2110747 prefixEnd_2110747 1083827751035758426355357 := by
  unfold tailWord_2110747
  simp only [CollatzResearch.WordTrace]
  refine ⟨76985267684131580732882495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51323511789421053821921663 76985267684131580732882495)
  ·
    refine ⟨115477901526197371099323743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76985267684131580732882495 115477901526197371099323743)
    ·
      refine ⟨173216852289296056648985615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115477901526197371099323743 173216852289296056648985615)
      ·
        refine ⟨259825278433944084973478423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173216852289296056648985615 259825278433944084973478423)
        ·
          refine ⟨389737917650916127460217635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259825278433944084973478423 389737917650916127460217635)
          ·
            refine ⟨584606876476374191190326453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389737917650916127460217635 584606876476374191190326453)
            ·
              refine ⟨54806894669660080424093105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 584606876476374191190326453 54806894669660080424093105)
              ·
                refine ⟨41105171002245060318069829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54806894669660080424093105 41105171002245060318069829)
                ·
                  refine ⟨7707219562920948809638093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41105171002245060318069829 7707219562920948809638093)
                  ·
                    refine ⟨2890207336095355803614285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7707219562920948809638093 2890207336095355803614285)
                    ·
                      refine ⟨1083827751035758426355357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890207336095355803614285 1083827751035758426355357)
                      ·
                        rfl

theorem cell23_2110747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3].length) (baseStart_2110747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110747 prefixEnd_2110747 := by exact prefixLift 2110747
  have htrace : WordTrace (prefixWord ++ tailWord_2110747) baseStart_2110747 baseEnd_2110747 := by
    simpa [prefixWord, tailWord_2110747, baseEnd_2110747] using wordTrace_append hprefix tailTrace_2110747
  have hstable : (prefixWord ++ tailWord_2110747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110747).length < 2 ^ (prefixWord ++ tailWord_2110747).sum := by decide
  have hdescent : baseEnd_2110747 < baseStart_2110747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110765 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2110765 : Nat := 118140960795 + 2110765 * 2 ^ 59
def prefixEnd_2110765 : Nat := 4983230072969 + 3 ^ 40 * 2110765 * 2
def baseEnd_2110765 : Nat := 1083836993687539355930275

theorem tailTrace_2110765 : CollatzResearch.WordTrace tailWord_2110765 prefixEnd_2110765 1083836993687539355930275 := by
  unfold tailWord_2110765
  simp only [CollatzResearch.WordTrace]
  refine ⟨76985924198066369807037749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51323949465377579871358499 76985924198066369807037749)
  ·
    refine ⟨7217430393568722169409789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76985924198066369807037749 7217430393568722169409789)
    ·
      refine ⟨2706536397588270813528671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7217430393568722169409789 2706536397588270813528671)
      ·
        refine ⟨4059804596382406220293007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706536397588270813528671 4059804596382406220293007)
        ·
          refine ⟨6089706894573609330439511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059804596382406220293007 6089706894573609330439511)
          ·
            refine ⟨9134560341860413995659267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089706894573609330439511 9134560341860413995659267)
            ·
              refine ⟨13701840512790620993488901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9134560341860413995659267 13701840512790620993488901)
              ·
                refine ⟨2569095096148241436279169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13701840512790620993488901 2569095096148241436279169)
                ·
                  refine ⟨1926821322111181077209377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569095096148241436279169 1926821322111181077209377)
                  ·
                    refine ⟨1445115991583385807907033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1926821322111181077209377 1445115991583385807907033)
                    ·
                      refine ⟨1083836993687539355930275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445115991583385807907033 1083836993687539355930275)
                      ·
                        rfl

theorem cell23_2110765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2110765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110765 prefixEnd_2110765 := by exact prefixLift 2110765
  have htrace : WordTrace (prefixWord ++ tailWord_2110765) baseStart_2110765 baseEnd_2110765 := by
    simpa [prefixWord, tailWord_2110765, baseEnd_2110765] using wordTrace_append hprefix tailTrace_2110765
  have hstable : (prefixWord ++ tailWord_2110765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110765).length < 2 ^ (prefixWord ++ tailWord_2110765).sum := by decide
  have hdescent : baseEnd_2110765 < baseStart_2110765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110771 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 5]
def baseStart_2110771 : Nat := 118140960795 + 2110771 * 2 ^ 59
def prefixEnd_2110771 : Nat := 4983230072969 + 3 ^ 40 * 2110771 * 2
def baseEnd_2110771 : Nat := 120426674952385148050583

theorem tailTrace_2110771 : CollatzResearch.WordTrace tailWord_2110771 prefixEnd_2110771 120426674952385148050583 := by
  unfold tailWord_2110771
  simp only [CollatzResearch.WordTrace]
  refine ⟨76986143036044632831756167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51324095357363088554504111 76986143036044632831756167)
  ·
    refine ⟨115479214554066949247634251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76986143036044632831756167 115479214554066949247634251)
    ·
      refine ⟨173218821831100423871451377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115479214554066949247634251 173218821831100423871451377)
      ·
        refine ⟨129914116373325317903588533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173218821831100423871451377 129914116373325317903588533)
        ·
          refine ⟨12179448409999248553461425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129914116373325317903588533 12179448409999248553461425)
          ·
            refine ⟨9134586307499436415096069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12179448409999248553461425 9134586307499436415096069)
            ·
              refine ⟨1712734932656144327830513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9134586307499436415096069 1712734932656144327830513)
              ·
                refine ⟨1284551199492108245872885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712734932656144327830513 1284551199492108245872885)
                ·
                  refine ⟨120426674952385148050583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1284551199492108245872885 120426674952385148050583)
                  ·
                    rfl

theorem cell23_2110771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 5].length) (baseStart_2110771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110771 prefixEnd_2110771 := by exact prefixLift 2110771
  have htrace : WordTrace (prefixWord ++ tailWord_2110771) baseStart_2110771 baseEnd_2110771 := by
    simpa [prefixWord, tailWord_2110771, baseEnd_2110771] using wordTrace_append hprefix tailTrace_2110771
  have hstable : (prefixWord ++ tailWord_2110771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110771).length < 2 ^ (prefixWord ++ tailWord_2110771).sum := by decide
  have hdescent : baseEnd_2110771 < baseStart_2110771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110787 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_2110787 : Nat := 118140960795 + 2110787 * 2 ^ 59
def prefixEnd_2110787 : Nat := 4983230072969 + 3 ^ 40 * 2110787 * 2
def baseEnd_2110787 : Nat := 1083848290261938269855173

theorem tailTrace_2110787 : CollatzResearch.WordTrace tailWord_2110787 prefixEnd_2110787 1083848290261938269855173 := by
  unfold tailWord_2110787
  simp only [CollatzResearch.WordTrace]
  refine ⟨76986726603986667564338615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51324484402657778376225743 76986726603986667564338615)
  ·
    refine ⟨115480089905980001346507923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76986726603986667564338615 115480089905980001346507923)
    ·
      refine ⟨173220134858970002019761885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115480089905980001346507923 173220134858970002019761885)
      ·
        refine ⟨64957550572113750757410707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173220134858970002019761885 64957550572113750757410707)
        ·
          refine ⟨97436325858170626136116061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64957550572113750757410707 97436325858170626136116061)
          ·
            refine ⟨36538622196813984801043523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97436325858170626136116061 36538622196813984801043523)
            ·
              refine ⟨54807933295220977201565285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36538622196813984801043523 54807933295220977201565285)
              ·
                refine ⟨10276487492853933225293491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54807933295220977201565285 10276487492853933225293491)
                ·
                  refine ⟨15414731239280899837940237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10276487492853933225293491 15414731239280899837940237)
                  ·
                    refine ⟨5780524214730337439227589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15414731239280899837940237 5780524214730337439227589)
                    ·
                      refine ⟨1083848290261938269855173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5780524214730337439227589 1083848290261938269855173)
                      ·
                        rfl

theorem cell23_2110787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_2110787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110787 prefixEnd_2110787 := by exact prefixLift 2110787
  have htrace : WordTrace (prefixWord ++ tailWord_2110787) baseStart_2110787 baseEnd_2110787 := by
    simpa [prefixWord, tailWord_2110787, baseEnd_2110787] using wordTrace_append hprefix tailTrace_2110787
  have hstable : (prefixWord ++ tailWord_2110787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110787).length < 2 ^ (prefixWord ++ tailWord_2110787).sum := by decide
  have hdescent : baseEnd_2110787 < baseStart_2110787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110804 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2110804 : Nat := 118140960795 + 2110804 * 2 ^ 59
def prefixEnd_2110804 : Nat := 4983230072969 + 3 ^ 40 * 2110804 * 2
def baseEnd_2110804 : Nat := 1083857019433064703342595

theorem tailTrace_2110804 : CollatzResearch.WordTrace tailWord_2110804 prefixEnd_2110804 1083857019433064703342595 := by
  unfold tailWord_2110804
  simp only [CollatzResearch.WordTrace]
  refine ⟨38493673322462539733853733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51324897763283386311804977 38493673322462539733853733)
  ·
    refine ⟨7217563747961726200097575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38493673322462539733853733 7217563747961726200097575)
    ·
      refine ⟨10826345621942589300146363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7217563747961726200097575 10826345621942589300146363)
      ·
        refine ⟨16239518432913883950219545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10826345621942589300146363 16239518432913883950219545)
        ·
          refine ⟨12179638824685412962664659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16239518432913883950219545 12179638824685412962664659)
          ·
            refine ⟨18269458237028119443996989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12179638824685412962664659 18269458237028119443996989)
            ·
              refine ⟨6851046838885544791498871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18269458237028119443996989 6851046838885544791498871)
              ·
                refine ⟨10276570258328317187248307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6851046838885544791498871 10276570258328317187248307)
                ·
                  refine ⟨15414855387492475780872461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10276570258328317187248307 15414855387492475780872461)
                  ·
                    refine ⟨5780570770309678417827173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15414855387492475780872461 5780570770309678417827173)
                    ·
                      refine ⟨1083857019433064703342595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5780570770309678417827173 1083857019433064703342595)
                      ·
                        rfl

theorem cell23_2110804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2110804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110804 prefixEnd_2110804 := by exact prefixLift 2110804
  have htrace : WordTrace (prefixWord ++ tailWord_2110804) baseStart_2110804 baseEnd_2110804 := by
    simpa [prefixWord, tailWord_2110804, baseEnd_2110804] using wordTrace_append hprefix tailTrace_2110804
  have hstable : (prefixWord ++ tailWord_2110804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110804).length < 2 ^ (prefixWord ++ tailWord_2110804).sum := by decide
  have hdescent : baseEnd_2110804 < baseStart_2110804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110817 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_2110817 : Nat := 118140960795 + 2110817 * 2 ^ 59
def prefixEnd_2110817 : Nat := 4983230072969 + 3 ^ 40 * 2110817 * 2
def baseEnd_2110817 : Nat := 1083863694681573152480035

theorem tailTrace_2110817 : CollatzResearch.WordTrace tailWord_2110817 prefixEnd_2110817 1083863694681573152480035 := by
  unfold tailWord_2110817
  simp only [CollatzResearch.WordTrace]
  refine ⟨76987820793877982687930705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51325213862585321791953803 76987820793877982687930705)
  ·
    refine ⟨57740865595408487015948029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76987820793877982687930705 57740865595408487015948029)
    ·
      refine ⟨21652824598278182630980511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57740865595408487015948029 21652824598278182630980511)
      ·
        refine ⟨32479236897417273946470767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21652824598278182630980511 32479236897417273946470767)
        ·
          refine ⟨48718855346125910919706151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32479236897417273946470767 48718855346125910919706151)
          ·
            refine ⟨73078283019188866379559227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48718855346125910919706151 73078283019188866379559227)
            ·
              refine ⟨109617424528783299569338841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73078283019188866379559227 109617424528783299569338841)
              ·
                refine ⟨82213068396587474677004131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109617424528783299569338841 82213068396587474677004131)
                ·
                  refine ⟨123319602594881212015506197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82213068396587474677004131 123319602594881212015506197)
                  ·
                    refine ⟨5780606371635056813226853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123319602594881212015506197 5780606371635056813226853)
                    ·
                      refine ⟨1083863694681573152480035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5780606371635056813226853 1083863694681573152480035)
                      ·
                        rfl

theorem cell23_2110817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_2110817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110817 prefixEnd_2110817 := by exact prefixLift 2110817
  have htrace : WordTrace (prefixWord ++ tailWord_2110817) baseStart_2110817 baseEnd_2110817 := by
    simpa [prefixWord, tailWord_2110817, baseEnd_2110817] using wordTrace_append hprefix tailTrace_2110817
  have hstable : (prefixWord ++ tailWord_2110817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110817).length < 2 ^ (prefixWord ++ tailWord_2110817).sum := by decide
  have hdescent : baseEnd_2110817 < baseStart_2110817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110831 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 1, 4]
def baseStart_2110831 : Nat := 118140960795 + 2110831 * 2 ^ 59
def prefixEnd_2110831 : Nat := 4983230072969 + 3 ^ 40 * 2110831 * 2
def baseEnd_2110831 : Nat := 361290294470245365901657

theorem tailTrace_2110831 : CollatzResearch.WordTrace tailWord_2110831 prefixEnd_2110831 361290294470245365901657 := by
  unfold tailWord_2110831
  simp only [CollatzResearch.WordTrace]
  refine ⟨76988331415827263078940347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51325554277218175385960231 76988331415827263078940347)
  ·
    refine ⟨115482497123740894618410521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76988331415827263078940347 115482497123740894618410521)
    ·
      refine ⟨86611872842805670963807891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115482497123740894618410521 86611872842805670963807891)
      ·
        refine ⟨129917809264208506445711837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86611872842805670963807891 129917809264208506445711837)
        ·
          refine ⟨48719178474078189917141939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129917809264208506445711837 48719178474078189917141939)
          ·
            refine ⟨73078767711117284875712909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48719178474078189917141939 73078767711117284875712909)
            ·
              refine ⟨27404537891668981828392341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73078767711117284875712909 27404537891668981828392341)
              ·
                refine ⟨1284587713671983523205891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27404537891668981828392341 1284587713671983523205891)
                ·
                  refine ⟨1926881570507975284808837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284587713671983523205891 1926881570507975284808837)
                  ·
                    refine ⟨361290294470245365901657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926881570507975284808837 361290294470245365901657)
                    ·
                      rfl

theorem cell23_2110831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 4].length) (baseStart_2110831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110831 prefixEnd_2110831 := by exact prefixLift 2110831
  have htrace : WordTrace (prefixWord ++ tailWord_2110831) baseStart_2110831 baseEnd_2110831 := by
    simpa [prefixWord, tailWord_2110831, baseEnd_2110831] using wordTrace_append hprefix tailTrace_2110831
  have hstable : (prefixWord ++ tailWord_2110831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110831).length < 2 ^ (prefixWord ++ tailWord_2110831).sum := by decide
  have hdescent : baseEnd_2110831 < baseStart_2110831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110938 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_2110938 : Nat := 118140960795 + 2110938 * 2 ^ 59
def prefixEnd_2110938 : Nat := 4983230072969 + 3 ^ 40 * 2110938 * 2
def baseEnd_2110938 : Nat := 361308608613589059688993

theorem tailTrace_2110938 : CollatzResearch.WordTrace tailWord_2110938 prefixEnd_2110938 361308608613589059688993 := by
  unfold tailWord_2110938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248058506609905088271367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51328156017626413568723645 19248058506609905088271367)
  ·
    refine ⟨28872087759914857632407051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19248058506609905088271367 28872087759914857632407051)
    ·
      refine ⟨43308131639872286448610577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28872087759914857632407051 43308131639872286448610577)
      ·
        refine ⟨32481098729904214836457933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43308131639872286448610577 32481098729904214836457933)
        ·
          refine ⟨12180412023714080563671725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32481098729904214836457933 12180412023714080563671725)
          ·
            refine ⟨4567654508892780211376897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12180412023714080563671725 4567654508892780211376897)
            ·
              refine ⟨3425740881669585158532673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567654508892780211376897 3425740881669585158532673)
              ·
                refine ⟨2569305661252188868899505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425740881669585158532673 2569305661252188868899505)
                ·
                  refine ⟨1926979245939141651674629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569305661252188868899505 1926979245939141651674629)
                  ·
                    refine ⟨361308608613589059688993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926979245939141651674629 361308608613589059688993)
                    ·
                      rfl

theorem cell23_2110938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_2110938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110938 prefixEnd_2110938 := by exact prefixLift 2110938
  have htrace : WordTrace (prefixWord ++ tailWord_2110938) baseStart_2110938 baseEnd_2110938 := by
    simpa [prefixWord, tailWord_2110938, baseEnd_2110938] using wordTrace_append hprefix tailTrace_2110938
  have hstable : (prefixWord ++ tailWord_2110938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110938).length < 2 ^ (prefixWord ++ tailWord_2110938).sum := by decide
  have hdescent : baseEnd_2110938 < baseStart_2110938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110951 : List Nat := [1, 1, 5, 2, 1, 4, 1, 8]
def baseStart_2110951 : Nat := 118140960795 + 2110951 * 2 ^ 59
def prefixEnd_2110951 : Nat := 4983230072969 + 3 ^ 40 * 2110951 * 2
def baseEnd_2110951 : Nat := 40145648188491689933497

theorem tailTrace_2110951 : CollatzResearch.WordTrace tailWord_2110951 prefixEnd_2110951 40145648188491689933497 := by
  unfold tailWord_2110951
  simp only [CollatzResearch.WordTrace]
  refine ⟨76992708175392523573308707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51328472116928349048872471 76992708175392523573308707)
  ·
    refine ⟨115489062263088785359963061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76992708175392523573308707 115489062263088785359963061)
    ·
      refine ⟨10827099587164573627496537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115489062263088785359963061 10827099587164573627496537)
      ·
        refine ⟨8120324690373430220622403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10827099587164573627496537 8120324690373430220622403)
        ·
          refine ⟨12180487035560145330933605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8120324690373430220622403 12180487035560145330933605)
          ·
            refine ⟨2283841319167527249550051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12180487035560145330933605 2283841319167527249550051)
            ·
              refine ⟨3425761978751290874325077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283841319167527249550051 3425761978751290874325077)
              ·
                refine ⟨40145648188491689933497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3425761978751290874325077 40145648188491689933497)
                ·
                  rfl

theorem cell23_2110951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 8].length) (baseStart_2110951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110951 prefixEnd_2110951 := by exact prefixLift 2110951
  have htrace : WordTrace (prefixWord ++ tailWord_2110951) baseStart_2110951 baseEnd_2110951 := by
    simpa [prefixWord, tailWord_2110951, baseEnd_2110951] using wordTrace_append hprefix tailTrace_2110951
  have hstable : (prefixWord ++ tailWord_2110951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110951).length < 2 ^ (prefixWord ++ tailWord_2110951).sum := by decide
  have hdescent : baseEnd_2110951 < baseStart_2110951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110961 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_2110961 : Nat := 118140960795 + 2110961 * 2 ^ 59
def prefixEnd_2110961 : Nat := 4983230072969 + 3 ^ 40 * 2110961 * 2
def baseEnd_2110961 : Nat := 1083937635895820589079373

theorem tailTrace_2110961 : CollatzResearch.WordTrace tailWord_2110961 prefixEnd_2110961 1083937635895820589079373 := by
  unfold tailWord_2110961
  simp only [CollatzResearch.WordTrace]
  refine ⟨76993072905356295281172737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51328715270237530187448491 76993072905356295281172737)
  ·
    refine ⟨57744804679017221460879553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76993072905356295281172737 57744804679017221460879553)
    ·
      refine ⟨43308603509262916095659665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57744804679017221460879553 43308603509262916095659665)
      ·
        refine ⟨32481452631947187071744749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43308603509262916095659665 32481452631947187071744749)
        ·
          refine ⟨12180544736980195151904281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32481452631947187071744749 12180544736980195151904281)
          ·
            refine ⟨9135408552735146363928211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12180544736980195151904281 9135408552735146363928211)
            ·
              refine ⟨13703112829102719545892317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9135408552735146363928211 13703112829102719545892317)
              ·
                refine ⟨5138667310913519829709619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13703112829102719545892317 5138667310913519829709619)
                ·
                  refine ⟨7708000966370279744564429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5138667310913519829709619 7708000966370279744564429)
                  ·
                    refine ⟨2890500362388854904211661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7708000966370279744564429 2890500362388854904211661)
                    ·
                      refine ⟨1083937635895820589079373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890500362388854904211661 1083937635895820589079373)
                      ·
                        rfl

theorem cell23_2110961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_2110961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110961 prefixEnd_2110961 := by exact prefixLift 2110961
  have htrace : WordTrace (prefixWord ++ tailWord_2110961) baseStart_2110961 baseEnd_2110961 := by
    simpa [prefixWord, tailWord_2110961, baseEnd_2110961] using wordTrace_append hprefix tailTrace_2110961
  have hstable : (prefixWord ++ tailWord_2110961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110961).length < 2 ^ (prefixWord ++ tailWord_2110961).sum := by decide
  have hdescent : baseEnd_2110961 < baseStart_2110961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110989 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2110989 : Nat := 118140960795 + 2110989 * 2 ^ 59
def prefixEnd_2110989 : Nat := 4983230072969 + 3 ^ 40 * 2110989 * 2
def baseEnd_2110989 : Nat := 361317337784715493176415

theorem tailTrace_2110989 : CollatzResearch.WordTrace tailWord_2110989 prefixEnd_2110989 361317337784715493176415 := by
  unfold tailWord_2110989
  simp only [CollatzResearch.WordTrace]
  refine ⟨76994094149254856063192021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51329396099503237375461347 76994094149254856063192021)
  ·
    refine ⟨1804549081623160688981063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 76994094149254856063192021 1804549081623160688981063)
    ·
      refine ⟨2706823622434741033471595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804549081623160688981063 2706823622434741033471595)
      ·
        refine ⟨4060235433652111550207393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706823622434741033471595 4060235433652111550207393)
        ·
          refine ⟨3045176575239083662655545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4060235433652111550207393 3045176575239083662655545)
          ·
            refine ⟨2283882431429312746991659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3045176575239083662655545 2283882431429312746991659)
            ·
              refine ⟨3425823647143969120487489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283882431429312746991659 3425823647143969120487489)
              ·
                refine ⟨2569367735357976840365617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425823647143969120487489 2569367735357976840365617)
                ·
                  refine ⟨1927025801518482630274213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569367735357976840365617 1927025801518482630274213)
                  ·
                    refine ⟨361317337784715493176415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927025801518482630274213 361317337784715493176415)
                    ·
                      rfl

theorem cell23_2110989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2110989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110989 prefixEnd_2110989 := by exact prefixLift 2110989
  have htrace : WordTrace (prefixWord ++ tailWord_2110989) baseStart_2110989 baseEnd_2110989 := by
    simpa [prefixWord, tailWord_2110989, baseEnd_2110989] using wordTrace_append hprefix tailTrace_2110989
  have hstable : (prefixWord ++ tailWord_2110989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110989).length < 2 ^ (prefixWord ++ tailWord_2110989).sum := by decide
  have hdescent : baseEnd_2110989 < baseStart_2110989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110995 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 3]
def baseStart_2110995 : Nat := 118140960795 + 2110995 * 2 ^ 59
def prefixEnd_2110995 : Nat := 4983230072969 + 3 ^ 40 * 2110995 * 2
def baseEnd_2110995 : Nat := 1083955094238073456054217

theorem tailTrace_2110995 : CollatzResearch.WordTrace tailWord_2110995 prefixEnd_2110995 1083955094238073456054217 := by
  unfold tailWord_2110995
  simp only [CollatzResearch.WordTrace]
  refine ⟨76994312987233119087910439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51329541991488746058606959 76994312987233119087910439)
  ·
    refine ⟨115491469480849678631865659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76994312987233119087910439 115491469480849678631865659)
    ·
      refine ⟨173237204221274517947798489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115491469480849678631865659 173237204221274517947798489)
      ·
        refine ⟨129927903165955888460848867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173237204221274517947798489 129927903165955888460848867)
        ·
          refine ⟨194891854748933832691273301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129927903165955888460848867 194891854748933832691273301)
          ·
            refine ⟨2283888922839068351850859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 194891854748933832691273301 2283888922839068351850859)
            ·
              refine ⟨3425833384258602527776289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283888922839068351850859 3425833384258602527776289)
              ·
                refine ⟨2569375038193951895832217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425833384258602527776289 2569375038193951895832217)
                ·
                  refine ⟨1927031278645463921874163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569375038193951895832217 1927031278645463921874163)
                  ·
                    refine ⟨2890546917968195882811245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927031278645463921874163 2890546917968195882811245)
                    ·
                      refine ⟨1083955094238073456054217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890546917968195882811245 1083955094238073456054217)
                      ·
                        rfl

theorem cell23_2110995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_2110995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2110995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2110995 prefixEnd_2110995 := by exact prefixLift 2110995
  have htrace : WordTrace (prefixWord ++ tailWord_2110995) baseStart_2110995 baseEnd_2110995 := by
    simpa [prefixWord, tailWord_2110995, baseEnd_2110995] using wordTrace_append hprefix tailTrace_2110995
  have hstable : (prefixWord ++ tailWord_2110995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110995).length < 2 ^ (prefixWord ++ tailWord_2110995).sum := by decide
  have hdescent : baseEnd_2110995 < baseStart_2110995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111006 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2111006 : Nat := 118140960795 + 2111006 * 2 ^ 59
def prefixEnd_2111006 : Nat := 4983230072969 + 3 ^ 40 * 2111006 * 2
def baseEnd_2111006 : Nat := 361320247508424304338889

theorem tailTrace_2111006 : CollatzResearch.WordTrace tailWord_2111006 prefixEnd_2111006 361320247508424304338889 := by
  unfold tailWord_2111006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9624339273774158495820109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51329809460128845311040581 9624339273774158495820109)
  ·
    refine ⟨3609127227665309435932541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9624339273774158495820109 3609127227665309435932541)
    ·
      refine ⟨1353422710374491038474703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3609127227665309435932541 1353422710374491038474703)
      ·
        refine ⟨2030134065561736557712055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353422710374491038474703 2030134065561736557712055)
        ·
          refine ⟨3045201098342604836568083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030134065561736557712055 3045201098342604836568083)
          ·
            refine ⟨4567801647513907254852125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3045201098342604836568083 4567801647513907254852125)
            ·
              refine ⟨1712925617817715220569547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4567801647513907254852125 1712925617817715220569547)
              ·
                refine ⟨2569388426726572830854321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712925617817715220569547 2569388426726572830854321)
                ·
                  refine ⟨1927041320044929623140741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569388426726572830854321 1927041320044929623140741)
                  ·
                    refine ⟨361320247508424304338889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927041320044929623140741 361320247508424304338889)
                    ·
                      rfl

theorem cell23_2111006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2111006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111006 prefixEnd_2111006 := by exact prefixLift 2111006
  have htrace : WordTrace (prefixWord ++ tailWord_2111006) baseStart_2111006 baseEnd_2111006 := by
    simpa [prefixWord, tailWord_2111006, baseEnd_2111006] using wordTrace_append hprefix tailTrace_2111006
  have hstable : (prefixWord ++ tailWord_2111006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111006).length < 2 ^ (prefixWord ++ tailWord_2111006).sum := by decide
  have hdescent : baseEnd_2111006 < baseStart_2111006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111022 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2111022 : Nat := 118140960795 + 2111022 * 2 ^ 59
def prefixEnd_2111022 : Nat := 4983230072969 + 3 ^ 40 * 2111022 * 2
def baseEnd_2111022 : Nat := 1083968958215744850416593

theorem tailTrace_2111022 : CollatzResearch.WordTrace tailWord_2111022 prefixEnd_2111022 1083968958215744850416593 := by
  unfold tailWord_2111022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9624412219766912837392915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51330198505423535132762213 9624412219766912837392915)
  ·
    refine ⟨14436618329650369256089373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9624412219766912837392915 14436618329650369256089373)
    ·
      refine ⟨5413731873618888471033515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14436618329650369256089373 5413731873618888471033515)
      ·
        refine ⟨8120597810428332706550273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413731873618888471033515 8120597810428332706550273)
        ·
          refine ⟨6090448357821249529912705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8120597810428332706550273 6090448357821249529912705)
          ·
            refine ⟨4567836268365937147434529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6090448357821249529912705 4567836268365937147434529)
            ·
              refine ⟨3425877201274452860575897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567836268365937147434529 3425877201274452860575897)
              ·
                refine ⟨2569407900955839645431923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425877201274452860575897 2569407900955839645431923)
                ·
                  refine ⟨3854111851433759468147885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2569407900955839645431923 3854111851433759468147885)
                  ·
                    refine ⟨1445291944287659800555457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3854111851433759468147885 1445291944287659800555457)
                    ·
                      refine ⟨1083968958215744850416593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445291944287659800555457 1083968958215744850416593)
                      ·
                        rfl

theorem cell23_2111022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2111022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111022 prefixEnd_2111022 := by exact prefixLift 2111022
  have htrace : WordTrace (prefixWord ++ tailWord_2111022) baseStart_2111022 baseEnd_2111022 := by
    simpa [prefixWord, tailWord_2111022, baseEnd_2111022] using wordTrace_append hprefix tailTrace_2111022
  have hstable : (prefixWord ++ tailWord_2111022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111022).length < 2 ^ (prefixWord ++ tailWord_2111022).sum := by decide
  have hdescent : baseEnd_2111022 < baseStart_2111022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111058 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_2111058 : Nat := 118140960795 + 2111058 * 2 ^ 59
def prefixEnd_2111058 : Nat := 4983230072969 + 3 ^ 40 * 2111058 * 2
def baseEnd_2111058 : Nat := 120443049279922967729603

theorem tailTrace_2111058 : CollatzResearch.WordTrace tailWord_2111058 prefixEnd_2111058 120443049279922967729603 := by
  unfold tailWord_2111058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19249152696501220211863457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51331073857336587231635885 19249152696501220211863457)
  ·
    refine ⟨14436864522375915158897593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19249152696501220211863457 14436864522375915158897593)
    ·
      refine ⟨10827648391781936369173195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14436864522375915158897593 10827648391781936369173195)
      ·
        refine ⟨16241472587672904553759793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10827648391781936369173195 16241472587672904553759793)
        ·
          refine ⟨12181104440754678415319845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16241472587672904553759793 12181104440754678415319845)
          ·
            refine ⟨2283957082641502202872471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12181104440754678415319845 2283957082641502202872471)
            ·
              refine ⟨3425935623962253304308707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283957082641502202872471 3425935623962253304308707)
              ·
                refine ⟨5138903435943379956463061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425935623962253304308707 5138903435943379956463061)
                ·
                  refine ⟨120443049279922967729603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5138903435943379956463061 120443049279922967729603)
                  ·
                    rfl

theorem cell23_2111058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_2111058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111058 prefixEnd_2111058 := by exact prefixLift 2111058
  have htrace : WordTrace (prefixWord ++ tailWord_2111058) baseStart_2111058 baseEnd_2111058 := by
    simpa [prefixWord, tailWord_2111058, baseEnd_2111058] using wordTrace_append hprefix tailTrace_2111058
  have hstable : (prefixWord ++ tailWord_2111058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111058).length < 2 ^ (prefixWord ++ tailWord_2111058).sum := by decide
  have hdescent : baseEnd_2111058 < baseStart_2111058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111088 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_2111088 : Nat := 118140960795 + 2111088 * 2 ^ 59
def prefixEnd_2111088 : Nat := 4983230072969 + 3 ^ 40 * 2111088 * 2
def baseEnd_2111088 : Nat := 361334282646313864063763

theorem tailTrace_2111088 : CollatzResearch.WordTrace tailWord_2111088 prefixEnd_2111088 361334282646313864063763 := by
  unfold tailWord_2111088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38498852487948097985522959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51331803317264130647363945 38498852487948097985522959)
  ·
    refine ⟨57748278731922146978284439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38498852487948097985522959 57748278731922146978284439)
    ·
      refine ⟨86622418097883220467426659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57748278731922146978284439 86622418097883220467426659)
      ·
        refine ⟨129933627146824830701139989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86622418097883220467426659 129933627146824830701139989)
        ·
          refine ⟨6090638772507413939115937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129933627146824830701139989 6090638772507413939115937)
          ·
            refine ⟨4567979079380560454336953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6090638772507413939115937 4567979079380560454336953)
            ·
              refine ⟨3425984309535420340752715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567979079380560454336953 3425984309535420340752715)
              ·
                refine ⟨5138976464303130511129073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425984309535420340752715 5138976464303130511129073)
                ·
                  refine ⟨3854232348227347883346805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5138976464303130511129073 3854232348227347883346805)
                  ·
                    refine ⟨361334282646313864063763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3854232348227347883346805 361334282646313864063763)
                    ·
                      rfl

theorem cell23_2111088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_2111088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111088 prefixEnd_2111088 := by exact prefixLift 2111088
  have htrace : WordTrace (prefixWord ++ tailWord_2111088) baseStart_2111088 baseEnd_2111088 := by
    simpa [prefixWord, tailWord_2111088, baseEnd_2111088] using wordTrace_append hprefix tailTrace_2111088
  have hstable : (prefixWord ++ tailWord_2111088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111088).length < 2 ^ (prefixWord ++ tailWord_2111088).sum := by decide
  have hdescent : baseEnd_2111088 < baseStart_2111088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111175 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_2111175 : Nat := 118140960795 + 2111175 * 2 ^ 59
def prefixEnd_2111175 : Nat := 4983230072969 + 3 ^ 40 * 2111175 * 2
def baseEnd_2111175 : Nat := 1084047520755882751803389

theorem tailTrace_2111175 : CollatzResearch.WordTrace tailWord_2111175 prefixEnd_2111175 1084047520755882751803389 := by
  unfold tailWord_2111175
  simp only [CollatzResearch.WordTrace]
  refine ⟨77000878126581009829462979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51333918751054006552975319 77000878126581009829462979)
  ·
    refine ⟨115501317189871514744194469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77000878126581009829462979 115501317189871514744194469)
    ·
      refine ⟨21656496973100909014536463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115501317189871514744194469 21656496973100909014536463)
      ·
        refine ⟨32484745459651363521804695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21656496973100909014536463 32484745459651363521804695)
        ·
          refine ⟨48727118189477045282707043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32484745459651363521804695 48727118189477045282707043)
          ·
            refine ⟨73090677284215567924060565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48727118189477045282707043 73090677284215567924060565)
            ·
              refine ⟨3426125497697604746440339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73090677284215567924060565 3426125497697604746440339)
              ·
                refine ⟨5139188246546407119660509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426125497697604746440339 5139188246546407119660509)
                ·
                  refine ⟨1927195592454902669872691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5139188246546407119660509 1927195592454902669872691)
                  ·
                    refine ⟨2890793388682354004809037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927195592454902669872691 2890793388682354004809037)
                    ·
                      refine ⟨1084047520755882751803389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890793388682354004809037 1084047520755882751803389)
                      ·
                        rfl

theorem cell23_2111175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_2111175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111175 prefixEnd_2111175 := by exact prefixLift 2111175
  have htrace : WordTrace (prefixWord ++ tailWord_2111175) baseStart_2111175 baseEnd_2111175 := by
    simpa [prefixWord, tailWord_2111175, baseEnd_2111175] using wordTrace_append hprefix tailTrace_2111175
  have hstable : (prefixWord ++ tailWord_2111175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111175).length < 2 ^ (prefixWord ++ tailWord_2111175).sum := by decide
  have hdescent : baseEnd_2111175 < baseStart_2111175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111241 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_2111241 : Nat := 118140960795 + 2111241 * 2 ^ 59
def prefixEnd_2111241 : Nat := 4983230072969 + 3 ^ 40 * 2111241 * 2
def baseEnd_2111241 : Nat := 1084081410479079493578085

theorem tailTrace_2111241 : CollatzResearch.WordTrace tailWord_2111241 prefixEnd_2111241 1084081410479079493578085 := by
  unfold tailWord_2111241
  simp only [CollatzResearch.WordTrace]
  refine ⟨77003285344341903101365577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51335523562894602067577051 77003285344341903101365577)
  ·
    refine ⟨57752464008256427326024183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77003285344341903101365577 57752464008256427326024183)
    ·
      refine ⟨86628696012384640989036275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57752464008256427326024183 86628696012384640989036275)
      ·
        refine ⟨129943044018576961483554413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86628696012384640989036275 129943044018576961483554413)
        ·
          refine ⟨48728641506966360556332905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129943044018576961483554413 48728641506966360556332905)
          ·
            refine ⟨36546481130224770417249679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48728641506966360556332905 36546481130224770417249679)
            ·
              refine ⟨54819721695337155625874519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36546481130224770417249679 54819721695337155625874519)
              ·
                refine ⟨82229582543005733438811779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54819721695337155625874519 82229582543005733438811779)
                ·
                  refine ⟨123344373814508600158217669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82229582543005733438811779 123344373814508600158217669)
                  ·
                    refine ⟨23127070090220362529665813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123344373814508600158217669 23127070090220362529665813)
                    ·
                      refine ⟨1084081410479079493578085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23127070090220362529665813 1084081410479079493578085)
                      ·
                        rfl

theorem cell23_2111241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_2111241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111241 prefixEnd_2111241 := by exact prefixLift 2111241
  have htrace : WordTrace (prefixWord ++ tailWord_2111241) baseStart_2111241 baseEnd_2111241 := by
    simpa [prefixWord, tailWord_2111241, baseEnd_2111241] using wordTrace_append hprefix tailTrace_2111241
  have hstable : (prefixWord ++ tailWord_2111241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111241).length < 2 ^ (prefixWord ++ tailWord_2111241).sum := by decide
  have hdescent : baseEnd_2111241 < baseStart_2111241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111242 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_2111242 : Nat := 118140960795 + 2111242 * 2 ^ 59
def prefixEnd_2111242 : Nat := 4983230072969 + 3 ^ 40 * 2111242 * 2
def baseEnd_2111242 : Nat := 361360641319911329888527

theorem tailTrace_2111242 : CollatzResearch.WordTrace tailWord_2111242 prefixEnd_2111242 361360641319911329888527 := by
  unfold tailWord_2111242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19250830454334570068037995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51335547878225520181434653 19250830454334570068037995)
  ·
    refine ⟨28876245681501855102056993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19250830454334570068037995 28876245681501855102056993)
    ·
      refine ⟨21657184261126391326542745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28876245681501855102056993 21657184261126391326542745)
      ·
        refine ⟨16242888195844793494907059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21657184261126391326542745 16242888195844793494907059)
        ·
          refine ⟨24364332293767190242360589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16242888195844793494907059 24364332293767190242360589)
          ·
            refine ⟨9136624610162696340885221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24364332293767190242360589 9136624610162696340885221)
            ·
              refine ⟨1713117114405505563915979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9136624610162696340885221 1713117114405505563915979)
              ·
                refine ⟨2569675671608258345873969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713117114405505563915979 2569675671608258345873969)
                ·
                  refine ⟨1927256753706193759405477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569675671608258345873969 1927256753706193759405477)
                  ·
                    refine ⟨361360641319911329888527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927256753706193759405477 361360641319911329888527)
                    ·
                      rfl

theorem cell23_2111242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_2111242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111242 prefixEnd_2111242 := by exact prefixLift 2111242
  have htrace : WordTrace (prefixWord ++ tailWord_2111242) baseStart_2111242 baseEnd_2111242 := by
    simpa [prefixWord, tailWord_2111242, baseEnd_2111242] using wordTrace_append hprefix tailTrace_2111242
  have hstable : (prefixWord ++ tailWord_2111242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111242).length < 2 ^ (prefixWord ++ tailWord_2111242).sum := by decide
  have hdescent : baseEnd_2111242 < baseStart_2111242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111251 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 7]
def baseStart_2111251 : Nat := 118140960795 + 2111251 * 2 ^ 59
def prefixEnd_2111251 : Nat := 4983230072969 + 3 ^ 40 * 2111251 * 2
def baseEnd_2111251 : Nat := 361362181761874818151013

theorem tailTrace_2111251 : CollatzResearch.WordTrace tailWord_2111251 prefixEnd_2111251 361362181761874818151013 := by
  unfold tailWord_2111251
  simp only [CollatzResearch.WordTrace]
  refine ⟨77003650074305674809229607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51335766716203783206153071 77003650074305674809229607)
  ·
    refine ⟨115505475111458512213844411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77003650074305674809229607 115505475111458512213844411)
    ·
      refine ⟨173258212667187768320766617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115505475111458512213844411 173258212667187768320766617)
      ·
        refine ⟨129943659500390826240574963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173258212667187768320766617 129943659500390826240574963)
        ·
          refine ⟨194915489250586239360862445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129943659500390826240574963 194915489250586239360862445)
          ·
            refine ⟨73093308468969839760323417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194915489250586239360862445 73093308468969839760323417)
            ·
              refine ⟨54819981351727379820242563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73093308468969839760323417 54819981351727379820242563)
              ·
                refine ⟨82229972027591069730363845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54819981351727379820242563 82229972027591069730363845)
                ·
                  refine ⟨15418119755173325574443221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82229972027591069730363845 15418119755173325574443221)
                  ·
                    refine ⟨361362181761874818151013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15418119755173325574443221 361362181761874818151013)
                    ·
                      rfl

theorem cell23_2111251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_2111251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111251 prefixEnd_2111251 := by exact prefixLift 2111251
  have htrace : WordTrace (prefixWord ++ tailWord_2111251) baseStart_2111251 baseEnd_2111251 := by
    simpa [prefixWord, tailWord_2111251, baseEnd_2111251] using wordTrace_append hprefix tailTrace_2111251
  have hstable : (prefixWord ++ tailWord_2111251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111251).length < 2 ^ (prefixWord ++ tailWord_2111251).sum := by decide
  have hdescent : baseEnd_2111251 < baseStart_2111251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111265 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2111265 : Nat := 118140960795 + 2111265 * 2 ^ 59
def prefixEnd_2111265 : Nat := 4983230072969 + 3 ^ 40 * 2111265 * 2
def baseEnd_2111265 : Nat := 1084093734014787399677975

theorem tailTrace_2111265 : CollatzResearch.WordTrace tailWord_2111265 prefixEnd_2111265 1084093734014787399677975 := by
  unfold tailWord_2111265
  simp only [CollatzResearch.WordTrace]
  refine ⟨77004160696254955200239249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51336107130836636800159499 77004160696254955200239249)
  ·
    refine ⟨57753120522191216400179437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77004160696254955200239249 57753120522191216400179437)
    ·
      refine ⟨21657420195821706150067289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57753120522191216400179437 21657420195821706150067289)
      ·
        refine ⟨16243065146866279612550467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21657420195821706150067289 16243065146866279612550467)
        ·
          refine ⟨24364597720299419418825701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16243065146866279612550467 24364597720299419418825701)
          ·
            refine ⟨4568362072556141141029819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24364597720299419418825701 4568362072556141141029819)
            ·
              refine ⟨6852543108834211711544729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4568362072556141141029819 6852543108834211711544729)
              ·
                refine ⟨5139407331625658783658547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6852543108834211711544729 5139407331625658783658547)
                ·
                  refine ⟨7709110997438488175487821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5139407331625658783658547 7709110997438488175487821)
                  ·
                    refine ⟨2890916624039433065807933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7709110997438488175487821 2890916624039433065807933)
                    ·
                      refine ⟨1084093734014787399677975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890916624039433065807933 1084093734014787399677975)
                      ·
                        rfl

theorem cell23_2111265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2111265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111265 prefixEnd_2111265 := by exact prefixLift 2111265
  have htrace : WordTrace (prefixWord ++ tailWord_2111265) baseStart_2111265 baseEnd_2111265 := by
    simpa [prefixWord, tailWord_2111265, baseEnd_2111265] using wordTrace_append hprefix tailTrace_2111265
  have hstable : (prefixWord ++ tailWord_2111265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111265).length < 2 ^ (prefixWord ++ tailWord_2111265).sum := by decide
  have hdescent : baseEnd_2111265 < baseStart_2111265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111282 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2111282 : Nat := 118140960795 + 2111282 * 2 ^ 59
def prefixEnd_2111282 : Nat := 4983230072969 + 3 ^ 40 * 2111282 * 2
def baseEnd_2111282 : Nat := 1084102463185913833165397

theorem tailTrace_2111282 : CollatzResearch.WordTrace tailWord_2111282 prefixEnd_2111282 1084102463185913833165397 := by
  unfold tailWord_2111282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19251195184298341775902025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51336520491462244735738733 19251195184298341775902025)
  ·
    refine ⟨14438396388223756331926519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19251195184298341775902025 14438396388223756331926519)
    ·
      refine ⟨21657594582335634497889779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14438396388223756331926519 21657594582335634497889779)
      ·
        refine ⟨32486391873503451746834669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21657594582335634497889779 32486391873503451746834669)
        ·
          refine ⟨12182396952563794405063001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32486391873503451746834669 12182396952563794405063001)
          ·
            refine ⟨9136797714422845803797251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12182396952563794405063001 9136797714422845803797251)
            ·
              refine ⟨13705196571634268705695877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9136797714422845803797251 13705196571634268705695877)
              ·
                refine ⟨2569724357181425382317977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13705196571634268705695877 2569724357181425382317977)
                ·
                  refine ⟨1927293267886069036738483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569724357181425382317977 1927293267886069036738483)
                  ·
                    refine ⟨2890939901829103555107725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1927293267886069036738483 2890939901829103555107725)
                    ·
                      refine ⟨1084102463185913833165397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2890939901829103555107725 1084102463185913833165397)
                      ·
                        rfl

theorem cell23_2111282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2111282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111282 prefixEnd_2111282 := by exact prefixLift 2111282
  have htrace : WordTrace (prefixWord ++ tailWord_2111282) baseStart_2111282 baseEnd_2111282 := by
    simpa [prefixWord, tailWord_2111282, baseEnd_2111282] using wordTrace_append hprefix tailTrace_2111282
  have hstable : (prefixWord ++ tailWord_2111282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111282).length < 2 ^ (prefixWord ++ tailWord_2111282).sum := by decide
  have hdescent : baseEnd_2111282 < baseStart_2111282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111283 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 1, 2, 2]
def baseStart_2111283 : Nat := 118140960795 + 2111283 * 2 ^ 59
def prefixEnd_2111283 : Nat := 4983230072969 + 3 ^ 40 * 2111283 * 2
def baseEnd_2111283 : Nat := 1084102976666568329252893

theorem tailTrace_2111283 : CollatzResearch.WordTrace tailWord_2111283 prefixEnd_2111283 1084102976666568329252893 := by
  unfold tailWord_2111283
  simp only [CollatzResearch.WordTrace]
  refine ⟨77004817210189744274394503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51336544806793162849596335 77004817210189744274394503)
  ·
    refine ⟨115507225815284616411591755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77004817210189744274394503 115507225815284616411591755)
    ·
      refine ⟨173260838722926924617387633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115507225815284616411591755 173260838722926924617387633)
      ·
        refine ⟨129945629042195193463040725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173260838722926924617387633 129945629042195193463040725)
        ·
          refine ⟨3045600680676449846790017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 129945629042195193463040725 3045600680676449846790017)
          ·
            refine ⟨2284200510507337385092513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3045600680676449846790017 2284200510507337385092513)
            ·
              refine ⟨1713150382880503038819385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284200510507337385092513 1713150382880503038819385)
              ·
                refine ⟨1284862787160377279114539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713150382880503038819385 1284862787160377279114539)
                ·
                  refine ⟨1927294180740565918671809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284862787160377279114539 1927294180740565918671809)
                  ·
                    refine ⟨1445470635555424439003857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1927294180740565918671809 1445470635555424439003857)
                    ·
                      refine ⟨1084102976666568329252893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445470635555424439003857 1084102976666568329252893)
                      ·
                        rfl

theorem cell23_2111283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 2, 2].length) (baseStart_2111283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111283 prefixEnd_2111283 := by exact prefixLift 2111283
  have htrace : WordTrace (prefixWord ++ tailWord_2111283) baseStart_2111283 baseEnd_2111283 := by
    simpa [prefixWord, tailWord_2111283, baseEnd_2111283] using wordTrace_append hprefix tailTrace_2111283
  have hstable : (prefixWord ++ tailWord_2111283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111283).length < 2 ^ (prefixWord ++ tailWord_2111283).sum := by decide
  have hdescent : baseEnd_2111283 < baseStart_2111283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111288 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2111288 : Nat := 118140960795 + 2111288 * 2 ^ 59
def prefixEnd_2111288 : Nat := 4983230072969 + 3 ^ 40 * 2111288 * 2
def baseEnd_2111288 : Nat := 1084105544069840809690369

theorem tailTrace_2111288 : CollatzResearch.WordTrace tailWord_2111288 prefixEnd_2111288 1084105544069840809690369 := by
  unfold tailWord_2111288
  simp only [CollatzResearch.WordTrace]
  refine ⟨38502499787585815064163259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51336666383447753418884345 38502499787585815064163259)
  ·
    refine ⟨57753749681378722596244889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38502499787585815064163259 57753749681378722596244889)
    ·
      refine ⟨43315312261034041947183667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57753749681378722596244889 43315312261034041947183667)
      ·
        refine ⟨64972968391551062920775501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43315312261034041947183667 64972968391551062920775501)
        ·
          refine ⟨24364863146831648595290813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64972968391551062920775501 24364863146831648595290813)
          ·
            refine ⟨9136823680061868223234055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24364863146831648595290813 9136823680061868223234055)
            ·
              refine ⟨13705235520092802334851083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9136823680061868223234055 13705235520092802334851083)
              ·
                refine ⟨20557853280139203502276625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13705235520092802334851083 20557853280139203502276625)
                ·
                  refine ⟨15418389960104402626707469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20557853280139203502276625 15418389960104402626707469)
                  ·
                    refine ⟨5781896235039150985015301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15418389960104402626707469 5781896235039150985015301)
                    ·
                      refine ⟨1084105544069840809690369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5781896235039150985015301 1084105544069840809690369)
                      ·
                        rfl

theorem cell23_2111288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2111288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111288 prefixEnd_2111288 := by exact prefixLift 2111288
  have htrace : WordTrace (prefixWord ++ tailWord_2111288) baseStart_2111288 baseEnd_2111288 := by
    simpa [prefixWord, tailWord_2111288, baseEnd_2111288] using wordTrace_append hprefix tailTrace_2111288
  have hstable : (prefixWord ++ tailWord_2111288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111288).length < 2 ^ (prefixWord ++ tailWord_2111288).sum := by decide
  have hdescent : baseEnd_2111288 < baseStart_2111288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111309 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2111309 : Nat := 118140960795 + 2111309 * 2 ^ 59
def prefixEnd_2111309 : Nat := 4983230072969 + 3 ^ 40 * 2111309 * 2
def baseEnd_2111309 : Nat := 1084116327163585227527773

theorem tailTrace_2111309 : CollatzResearch.WordTrace tailWord_2111309 prefixEnd_2111309 1084116327163585227527773 := by
  unfold tailWord_2111309
  simp only [CollatzResearch.WordTrace]
  refine ⟨77005765508095550714840981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51337177005397033809893987 77005765508095550714840981)
  ·
    refine ⟨3609645258191978939758171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77005765508095550714840981 3609645258191978939758171)
    ·
      refine ⟨5414467887287968409637257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609645258191978939758171 5414467887287968409637257)
      ·
        refine ⟨4060850915465976307227943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5414467887287968409637257 4060850915465976307227943)
        ·
          refine ⟨6091276373198964460841915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4060850915465976307227943 6091276373198964460841915)
          ·
            refine ⟨9136914559798446691262873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091276373198964460841915 9136914559798446691262873)
            ·
              refine ⟨6852685919848835018447155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9136914559798446691262873 6852685919848835018447155)
              ·
                refine ⟨10279028879773252527670733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6852685919848835018447155 10279028879773252527670733)
                ·
                  refine ⟨3854635829914969697876525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10279028879773252527670733 3854635829914969697876525)
                  ·
                    refine ⟨1445488436218113636703697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3854635829914969697876525 1445488436218113636703697)
                    ·
                      refine ⟨1084116327163585227527773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445488436218113636703697 1084116327163585227527773)
                      ·
                        rfl

theorem cell23_2111309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2111309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111309 prefixEnd_2111309 := by exact prefixLift 2111309
  have htrace : WordTrace (prefixWord ++ tailWord_2111309) baseStart_2111309 baseEnd_2111309 := by
    simpa [prefixWord, tailWord_2111309, baseEnd_2111309] using wordTrace_append hprefix tailTrace_2111309
  have hstable : (prefixWord ++ tailWord_2111309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111309).length < 2 ^ (prefixWord ++ tailWord_2111309).sum := by decide
  have hdescent : baseEnd_2111309 < baseStart_2111309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111322 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_2111322 : Nat := 118140960795 + 2111322 * 2 ^ 59
def prefixEnd_2111322 : Nat := 4983230072969 + 3 ^ 40 * 2111322 * 2
def baseEnd_2111322 : Nat := 1084123002412093676665213

theorem tailTrace_2111322 : CollatzResearch.WordTrace tailWord_2111322 prefixEnd_2111322 1084123002412093676665213 := by
  unfold tailWord_2111322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19251559914262113483766055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51337493104698969290042813 19251559914262113483766055)
  ·
    refine ⟨28877339871393170225649083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19251559914262113483766055 28877339871393170225649083)
    ·
      refine ⟨43316009807089755338473625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28877339871393170225649083 43316009807089755338473625)
      ·
        refine ⟨32487007355317316503855219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43316009807089755338473625 32487007355317316503855219)
        ·
          refine ⟨48730511032975974755782829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32487007355317316503855219 48730511032975974755782829)
          ·
            refine ⟨18273941637365990533418561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48730511032975974755782829 18273941637365990533418561)
            ·
              refine ⟨13705456228024492900063921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18273941637365990533418561 13705456228024492900063921)
              ·
                refine ⟨10279092171018369675047941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13705456228024492900063921 10279092171018369675047941)
                ·
                  refine ⟨1927329782065944314071489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10279092171018369675047941 1927329782065944314071489)
                  ·
                    refine ⟨1445497336549458235553617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1927329782065944314071489 1445497336549458235553617)
                    ·
                      refine ⟨1084123002412093676665213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1445497336549458235553617 1084123002412093676665213)
                      ·
                        rfl

theorem cell23_2111322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_2111322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111322 prefixEnd_2111322 := by exact prefixLift 2111322
  have htrace : WordTrace (prefixWord ++ tailWord_2111322) baseStart_2111322 baseEnd_2111322 := by
    simpa [prefixWord, tailWord_2111322, baseEnd_2111322] using wordTrace_append hprefix tailTrace_2111322
  have hstable : (prefixWord ++ tailWord_2111322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111322).length < 2 ^ (prefixWord ++ tailWord_2111322).sum := by decide
  have hdescent : baseEnd_2111322 < baseStart_2111322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111345 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 5]
def baseStart_2111345 : Nat := 118140960795 + 2111345 * 2 ^ 59
def prefixEnd_2111345 : Nat := 4983230072969 + 3 ^ 40 * 2111345 * 2
def baseEnd_2111345 : Nat := 120459423607460787408623

theorem tailTrace_2111345 : CollatzResearch.WordTrace tailWord_2111345 prefixEnd_2111345 120459423607460787408623 := by
  unfold tailWord_2111345
  simp only [CollatzResearch.WordTrace]
  refine ⟨77007078535965128863151489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51338052357310085908767659 77007078535965128863151489)
  ·
    refine ⟨57755308901973846647363617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77007078535965128863151489 57755308901973846647363617)
    ·
      refine ⟨43316481676480384985522713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57755308901973846647363617 43316481676480384985522713)
      ·
        refine ⟨32487361257360288739142035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43316481676480384985522713 32487361257360288739142035)
        ·
          refine ⟨48731041886040433108713053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32487361257360288739142035 48731041886040433108713053)
          ·
            refine ⟨18274140707265162415767395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48731041886040433108713053 18274140707265162415767395)
            ·
              refine ⟨27411211060897743623651093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18274140707265162415767395 27411211060897743623651093)
              ·
                refine ⟨1284900518479581732358645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27411211060897743623651093 1284900518479581732358645)
                ·
                  refine ⟨120459423607460787408623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1284900518479581732358645 120459423607460787408623)
                  ·
                    rfl

theorem cell23_2111345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 5].length) (baseStart_2111345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111345 prefixEnd_2111345 := by exact prefixLift 2111345
  have htrace : WordTrace (prefixWord ++ tailWord_2111345) baseStart_2111345 baseEnd_2111345 := by
    simpa [prefixWord, tailWord_2111345, baseEnd_2111345] using wordTrace_append hprefix tailTrace_2111345
  have hstable : (prefixWord ++ tailWord_2111345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111345).length < 2 ^ (prefixWord ++ tailWord_2111345).sum := by decide
  have hdescent : baseEnd_2111345 < baseStart_2111345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111415 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_2111415 : Nat := 118140960795 + 2111415 * 2 ^ 59
def prefixEnd_2111415 : Nat := 4983230072969 + 3 ^ 40 * 2111415 * 2
def baseEnd_2111415 : Nat := 1084170756112961812802285

theorem tailTrace_2111415 : CollatzResearch.WordTrace tailWord_2111415 prefixEnd_2111415 1084170756112961812802285 := by
  unfold tailWord_2111415
  simp only [CollatzResearch.WordTrace]
  refine ⟨77009631645711530818199699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51339754430474353878799799 77009631645711530818199699)
  ·
    refine ⟨115514447468567296227299549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77009631645711530818199699 115514447468567296227299549)
    ·
      refine ⟨43317917800712736085237331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115514447468567296227299549 43317917800712736085237331)
      ·
        refine ⟨64976876701069104127855997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43317917800712736085237331 64976876701069104127855997)
        ·
          refine ⟨24366328762900914047945999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64976876701069104127855997 24366328762900914047945999)
          ·
            refine ⟨36549493144351371071918999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24366328762900914047945999 36549493144351371071918999)
            ·
              refine ⟨54824239716527056607878499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36549493144351371071918999 54824239716527056607878499)
              ·
                refine ⟨82236359574790584911817749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54824239716527056607878499 82236359574790584911817749)
                ·
                  refine ⟨3854829355068308667741457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82236359574790584911817749 3854829355068308667741457)
                  ·
                    refine ⟨2891122016301231500806093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3854829355068308667741457 2891122016301231500806093)
                    ·
                      refine ⟨1084170756112961812802285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891122016301231500806093 1084170756112961812802285)
                      ·
                        rfl

theorem cell23_2111415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_2111415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111415 prefixEnd_2111415 := by exact prefixLift 2111415
  have htrace : WordTrace (prefixWord ++ tailWord_2111415) baseStart_2111415 baseEnd_2111415 := by
    simpa [prefixWord, tailWord_2111415, baseEnd_2111415] using wordTrace_append hprefix tailTrace_2111415
  have hstable : (prefixWord ++ tailWord_2111415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111415).length < 2 ^ (prefixWord ++ tailWord_2111415).sum := by decide
  have hdescent : baseEnd_2111415 < baseStart_2111415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111418 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_2111418 : Nat := 118140960795 + 2111418 * 2 ^ 59
def prefixEnd_2111418 : Nat := 4983230072969 + 3 ^ 40 * 2111418 * 2
def baseEnd_2111418 : Nat := 120463588506102811229419

theorem tailTrace_2111418 : CollatzResearch.WordTrace tailWord_2111418 prefixEnd_2111418 120463588506102811229419 := by
  unfold tailWord_2111418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19252435266175165582639727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51339827376467108220372605 19252435266175165582639727)
  ·
    refine ⟨28878652899262748373959591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19252435266175165582639727 28878652899262748373959591)
    ·
      refine ⟨43317979348894122560939387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28878652899262748373959591 43317979348894122560939387)
      ·
        refine ⟨64976969023341183841409081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43317979348894122560939387 64976969023341183841409081)
        ·
          refine ⟨48732726767505887881056811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64976969023341183841409081 48732726767505887881056811)
          ·
            refine ⟨73099090151258831821585217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48732726767505887881056811 73099090151258831821585217)
            ·
              refine ⟨54824317613444123866188913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73099090151258831821585217 54824317613444123866188913)
              ·
                refine ⟨41118238210083092899641685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54824317613444123866188913 41118238210083092899641685)
                ·
                  refine ⟨120463588506102811229419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41118238210083092899641685 120463588506102811229419)
                  ·
                    rfl

theorem cell23_2111418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_2111418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111418 prefixEnd_2111418 := by exact prefixLift 2111418
  have htrace : WordTrace (prefixWord ++ tailWord_2111418) baseStart_2111418 baseEnd_2111418 := by
    simpa [prefixWord, tailWord_2111418, baseEnd_2111418] using wordTrace_append hprefix tailTrace_2111418
  have hstable : (prefixWord ++ tailWord_2111418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111418).length < 2 ^ (prefixWord ++ tailWord_2111418).sum := by decide
  have hdescent : baseEnd_2111418 < baseStart_2111418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111432 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_2111432 : Nat := 118140960795 + 2111432 * 2 ^ 59
def prefixEnd_2111432 : Nat := 4983230072969 + 3 ^ 40 * 2111432 * 2
def baseEnd_2111432 : Nat := 1084179485284088246289707

theorem tailTrace_2111432 : CollatzResearch.WordTrace tailWord_2111432 prefixEnd_2111432 1084179485284088246289707 := by
  unfold tailWord_2111432
  simp only [CollatzResearch.WordTrace]
  refine ⟨38505125843324971360784275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51340167791099961814379033 38505125843324971360784275)
  ·
    refine ⟨57757688764987457041176413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38505125843324971360784275 57757688764987457041176413)
    ·
      refine ⟨21659133286870296390441155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57757688764987457041176413 21659133286870296390441155)
      ·
        refine ⟨32488699930305444585661733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21659133286870296390441155 32488699930305444585661733)
        ·
          refine ⟨6091631236932270859811575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32488699930305444585661733 6091631236932270859811575)
          ·
            refine ⟨9137446855398406289717363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091631236932270859811575 9137446855398406289717363)
            ·
              refine ⟨13706170283097609434576045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9137446855398406289717363 13706170283097609434576045)
              ·
                refine ⟨5139813856161603537966017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13706170283097609434576045 5139813856161603537966017)
                ·
                  refine ⟨3854860392121202653474513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139813856161603537966017 3854860392121202653474513)
                  ·
                    refine ⟨2891145294090901990105885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3854860392121202653474513 2891145294090901990105885)
                    ·
                      refine ⟨1084179485284088246289707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2891145294090901990105885 1084179485284088246289707)
                      ·
                        rfl

theorem cell23_2111432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_2111432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2111432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2111432 prefixEnd_2111432 := by exact prefixLift 2111432
  have htrace : WordTrace (prefixWord ++ tailWord_2111432) baseStart_2111432 baseEnd_2111432 := by
    simpa [prefixWord, tailWord_2111432, baseEnd_2111432] using wordTrace_append hprefix tailTrace_2111432
  have hstable : (prefixWord ++ tailWord_2111432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111432).length < 2 ^ (prefixWord ++ tailWord_2111432).sum := by decide
  have hdescent : baseEnd_2111432 < baseStart_2111432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
