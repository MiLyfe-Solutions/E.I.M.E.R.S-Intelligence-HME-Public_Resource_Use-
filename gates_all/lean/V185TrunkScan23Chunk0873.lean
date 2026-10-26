import V185TrunkScan23Chunk0872

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5166685 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5166685 : Nat := 118140960795 + 5166685 * 2 ^ 59
def prefixEnd_5166685 : Nat := 4983230072969 + 3 ^ 40 * 5166685 * 2
def baseEnd_5166685 : Nat := 2652992795375223054876355

theorem tailTrace_5166685 : CollatzResearch.WordTrace tailWord_5166685 prefixEnd_5166685 2652992795375223054876355 := by
  unfold tailWord_5166685
  simp only [CollatzResearch.WordTrace]
  refine ⟨188444483286990119391693509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125629655524660079594462339 188444483286990119391693509)
  ·
    refine ⟨35333340616310647385942533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188444483286990119391693509 35333340616310647385942533)
    ·
      refine ⟨6625001365558246384864225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35333340616310647385942533 6625001365558246384864225)
      ·
        refine ⟨4968751024168684788648169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6625001365558246384864225 4968751024168684788648169)
        ·
          refine ⟨3726563268126513591486127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4968751024168684788648169 3726563268126513591486127)
          ·
            refine ⟨5589844902189770387229191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726563268126513591486127 5589844902189770387229191)
            ·
              refine ⟨8384767353284655580843787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589844902189770387229191 8384767353284655580843787)
              ·
                refine ⟨12577151029926983371265681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8384767353284655580843787 12577151029926983371265681)
                ·
                  refine ⟨9432863272445237528449261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12577151029926983371265681 9432863272445237528449261)
                  ·
                    refine ⟨3537323727166964073168473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9432863272445237528449261 3537323727166964073168473)
                    ·
                      refine ⟨2652992795375223054876355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537323727166964073168473 2652992795375223054876355)
                      ·
                        rfl

theorem cell23_5166685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5166685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166685 prefixEnd_5166685 := by exact prefixLift 5166685
  have htrace : WordTrace (prefixWord ++ tailWord_5166685) baseStart_5166685 baseEnd_5166685 := by
    simpa [prefixWord, tailWord_5166685, baseEnd_5166685] using wordTrace_append hprefix tailTrace_5166685
  have hstable : (prefixWord ++ tailWord_5166685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166685).length < 2 ^ (prefixWord ++ tailWord_5166685).sum := by decide
  have hdescent : baseEnd_5166685 < baseStart_5166685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166698 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5166698 : Nat := 118140960795 + 5166698 * 2 ^ 59
def prefixEnd_5166698 : Nat := 4983230072969 + 3 ^ 40 * 5166698 * 2
def baseEnd_5166698 : Nat := 2652999470623731504013795

theorem tailTrace_5166698 : CollatzResearch.WordTrace tailWord_5166698 prefixEnd_5166698 2652999470623731504013795 := by
  unfold tailWord_5166698
  simp only [CollatzResearch.WordTrace]
  refine ⟨47111239358985755652979187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125629971623962015074611165 47111239358985755652979187)
  ·
    refine ⟨70666859038478633479468781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47111239358985755652979187 70666859038478633479468781)
    ·
      refine ⟨26500072139429487554800793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70666859038478633479468781 26500072139429487554800793)
      ·
        refine ⟨19875054104572115666100595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26500072139429487554800793 19875054104572115666100595)
        ·
          refine ⟨29812581156858173499150893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19875054104572115666100595 29812581156858173499150893)
          ·
            refine ⟨11179717933821815062181585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29812581156858173499150893 11179717933821815062181585)
            ·
              refine ⟨8384788450366361296636189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11179717933821815062181585 8384788450366361296636189)
              ·
                refine ⟨3144295668887385486238571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8384788450366361296636189 3144295668887385486238571)
                ·
                  refine ⟨4716443503331078229357857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144295668887385486238571 4716443503331078229357857)
                  ·
                    refine ⟨3537332627498308672018393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716443503331078229357857 3537332627498308672018393)
                    ·
                      refine ⟨2652999470623731504013795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537332627498308672018393 2652999470623731504013795)
                      ·
                        rfl

theorem cell23_5166698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5166698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166698 prefixEnd_5166698 := by exact prefixLift 5166698
  have htrace : WordTrace (prefixWord ++ tailWord_5166698) baseStart_5166698 baseEnd_5166698 := by
    simpa [prefixWord, tailWord_5166698, baseEnd_5166698] using wordTrace_append hprefix tailTrace_5166698
  have hstable : (prefixWord ++ tailWord_5166698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166698).length < 2 ^ (prefixWord ++ tailWord_5166698).sum := by decide
  have hdescent : baseEnd_5166698 < baseStart_5166698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166737 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_5166737 : Nat := 118140960795 + 5166737 * 2 ^ 59
def prefixEnd_5166737 : Nat := 4983230072969 + 3 ^ 40 * 5166737 * 2
def baseEnd_5166737 : Nat := 2653019496369256851426115

theorem tailTrace_5166737 : CollatzResearch.WordTrace tailWord_5166737 prefixEnd_5166737 2653019496369256851426115 := by
  unfold tailWord_5166737
  simp only [CollatzResearch.WordTrace]
  refine ⟨188446379882801732272586465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125630919921867821515057643 188446379882801732272586465)
  ·
    refine ⟨141334784912101299204439849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188446379882801732272586465 141334784912101299204439849)
    ·
      refine ⟨106001088684075974403329887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141334784912101299204439849 106001088684075974403329887)
      ·
        refine ⟨159001633026113961604994831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106001088684075974403329887 159001633026113961604994831)
        ·
          refine ⟨238502449539170942407492247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159001633026113961604994831 238502449539170942407492247)
          ·
            refine ⟨357753674308756413611238371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238502449539170942407492247 357753674308756413611238371)
            ·
              refine ⟨536630511463134620416857557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357753674308756413611238371 536630511463134620416857557)
              ·
                refine ⟨12577277612417217666020099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 536630511463134620416857557 12577277612417217666020099)
                ·
                  refine ⟨18865916418625826499030149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12577277612417217666020099 18865916418625826499030149)
                  ·
                    refine ⟨3537359328492342468568153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18865916418625826499030149 3537359328492342468568153)
                    ·
                      refine ⟨2653019496369256851426115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537359328492342468568153 2653019496369256851426115)
                      ·
                        rfl

theorem cell23_5166737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_5166737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166737 prefixEnd_5166737 := by exact prefixLift 5166737
  have htrace : WordTrace (prefixWord ++ tailWord_5166737) baseStart_5166737 baseEnd_5166737 := by
    simpa [prefixWord, tailWord_5166737, baseEnd_5166737] using wordTrace_append hprefix tailTrace_5166737
  have hstable : (prefixWord ++ tailWord_5166737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166737).length < 2 ^ (prefixWord ++ tailWord_5166737).sum := by decide
  have hdescent : baseEnd_5166737 < baseStart_5166737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166777 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 5]
def baseStart_5166777 : Nat := 118140960795 + 5166777 * 2 ^ 59
def prefixEnd_5166777 : Nat := 4983230072969 + 3 ^ 40 * 5166777 * 2
def baseEnd_5166777 : Nat := 294782226177270743880659

theorem tailTrace_5166777 : CollatzResearch.WordTrace tailWord_5166777 prefixEnd_5166777 294782226177270743880659 := by
  unfold tailWord_5166777
  simp only [CollatzResearch.WordTrace]
  refine ⟨188447838802656819104042585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125631892535104546069361723 188447838802656819104042585)
  ·
    refine ⟨141335879101992614328031939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188447838802656819104042585 141335879101992614328031939)
    ·
      refine ⟨212003818652988921492047909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141335879101992614328031939 212003818652988921492047909)
      ·
        refine ⟨39750715997435422779758983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212003818652988921492047909 39750715997435422779758983)
        ·
          refine ⟨59626073996153134169638475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39750715997435422779758983 59626073996153134169638475)
          ·
            refine ⟨89439110994229701254457713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59626073996153134169638475 89439110994229701254457713)
            ·
              refine ⟨67079333245672275940843285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89439110994229701254457713 67079333245672275940843285)
              ·
                refine ⟨3144343745890887934727029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67079333245672275940843285 3144343745890887934727029)
                ·
                  refine ⟨294782226177270743880659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3144343745890887934727029 294782226177270743880659)
                  ·
                    rfl

theorem cell23_5166777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 5].length) (baseStart_5166777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166777 prefixEnd_5166777 := by exact prefixLift 5166777
  have htrace : WordTrace (prefixWord ++ tailWord_5166777) baseStart_5166777 baseEnd_5166777 := by
    simpa [prefixWord, tailWord_5166777, baseEnd_5166777] using wordTrace_append hprefix tailTrace_5166777
  have hstable : (prefixWord ++ tailWord_5166777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166777).length < 2 ^ (prefixWord ++ tailWord_5166777).sum := by decide
  have hdescent : baseEnd_5166777 < baseStart_5166777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166807 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 2, 5]
def baseStart_5166807 : Nat := 118140960795 + 5166807 * 2 ^ 59
def prefixEnd_5166807 : Nat := 4983230072969 + 3 ^ 40 * 5166807 * 2
def baseEnd_5166807 : Nat := 884351813338357192516931

theorem tailTrace_5166807 : CollatzResearch.WordTrace tailWord_5166807 prefixEnd_5166807 884351813338357192516931 := by
  unfold tailWord_5166807
  simp only [CollatzResearch.WordTrace]
  refine ⟨188448932992548134227634675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125632621995032089485089783 188448932992548134227634675)
  ·
    refine ⟨282673399488822201341452013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188448932992548134227634675 282673399488822201341452013)
    ·
      refine ⟨106002524808308325503044505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282673399488822201341452013 106002524808308325503044505)
      ·
        refine ⟨79501893606231244127283379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106002524808308325503044505 79501893606231244127283379)
        ·
          refine ⟨119252840409346866190925069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79501893606231244127283379 119252840409346866190925069)
          ·
            refine ⟨44719815153505074821596901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119252840409346866190925069 44719815153505074821596901)
            ·
              refine ⟨8384965341282201529049419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44719815153505074821596901 8384965341282201529049419)
              ·
                refine ⟨12577448011923302293574129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8384965341282201529049419 12577448011923302293574129)
                ·
                  refine ⟨9433086008942476720180597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12577448011923302293574129 9433086008942476720180597)
                  ·
                    refine ⟨884351813338357192516931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433086008942476720180597 884351813338357192516931)
                    ·
                      rfl

theorem cell23_5166807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_5166807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166807 prefixEnd_5166807 := by exact prefixLift 5166807
  have htrace : WordTrace (prefixWord ++ tailWord_5166807) baseStart_5166807 baseEnd_5166807 := by
    simpa [prefixWord, tailWord_5166807, baseEnd_5166807] using wordTrace_append hprefix tailTrace_5166807
  have hstable : (prefixWord ++ tailWord_5166807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166807).length < 2 ^ (prefixWord ++ tailWord_5166807).sum := by decide
  have hdescent : baseEnd_5166807 < baseStart_5166807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166827 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4]
def baseStart_5166827 : Nat := 118140960795 + 5166827 * 2 ^ 59
def prefixEnd_5166827 : Nat := 4983230072969 + 3 ^ 40 * 5166827 * 2
def baseEnd_5166827 : Nat := 2653065709628161499300701

theorem tailTrace_5166827 : CollatzResearch.WordTrace tailWord_5166827 prefixEnd_5166827 2653065709628161499300701 := by
  unfold tailWord_5166827
  simp only [CollatzResearch.WordTrace]
  refine ⟨188449662452475677643362735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125633108301650451762241823 188449662452475677643362735)
  ·
    refine ⟨282674493678713516465044103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188449662452475677643362735 282674493678713516465044103)
    ·
      refine ⟨424011740518070274697566155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282674493678713516465044103 424011740518070274697566155)
      ·
        refine ⟨636017610777105412046349233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424011740518070274697566155 636017610777105412046349233)
        ·
          refine ⟨477013208082829059034761925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636017610777105412046349233 477013208082829059034761925)
          ·
            refine ⟨89439976515530448569017861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 477013208082829059034761925 89439976515530448569017861)
            ·
              refine ⟨16769995596661959106690849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89439976515530448569017861 16769995596661959106690849)
              ·
                refine ⟨12577496697496469330018137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16769995596661959106690849 12577496697496469330018137)
                ·
                  refine ⟨9433122523122351997513603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12577496697496469330018137 9433122523122351997513603)
                  ·
                    refine ⟨14149683784683527996270405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9433122523122351997513603 14149683784683527996270405)
                    ·
                      refine ⟨2653065709628161499300701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14149683784683527996270405 2653065709628161499300701)
                      ·
                        rfl

theorem cell23_5166827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4].length) (baseStart_5166827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166827 prefixEnd_5166827 := by exact prefixLift 5166827
  have htrace : WordTrace (prefixWord ++ tailWord_5166827) baseStart_5166827 baseEnd_5166827 := by
    simpa [prefixWord, tailWord_5166827, baseEnd_5166827] using wordTrace_append hprefix tailTrace_5166827
  have hstable : (prefixWord ++ tailWord_5166827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166827).length < 2 ^ (prefixWord ++ tailWord_5166827).sum := by decide
  have hdescent : baseEnd_5166827 < baseStart_5166827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166840 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_5166840 : Nat := 118140960795 + 5166840 * 2 ^ 59
def prefixEnd_5166840 : Nat := 4983230072969 + 3 ^ 40 * 5166840 * 2
def baseEnd_5166840 : Nat := 2653072384876669948438141

theorem tailTrace_5166840 : CollatzResearch.WordTrace tailWord_5166840 prefixEnd_5166840 2653072384876669948438141 := by
  unfold tailWord_5166840
  simp only [CollatzResearch.WordTrace]
  refine ⟨94225068300714290431792987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125633424400952387242390649 94225068300714290431792987)
  ·
    refine ⟨141337602451071435647689481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94225068300714290431792987 141337602451071435647689481)
    ·
      refine ⟨106003201838303576735767111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141337602451071435647689481 106003201838303576735767111)
      ·
        refine ⟨159004802757455365103650667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106003201838303576735767111 159004802757455365103650667)
        ·
          refine ⟨238507204136183047655476001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159004802757455365103650667 238507204136183047655476001)
          ·
            refine ⟨178880403102137285741607001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238507204136183047655476001 178880403102137285741607001)
            ·
              refine ⟨134160302326602964306205251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178880403102137285741607001 134160302326602964306205251)
              ·
                refine ⟨201240453489904446459307877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134160302326602964306205251 201240453489904446459307877)
                ·
                  refine ⟨37732585029357083711120227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201240453489904446459307877 37732585029357083711120227)
                  ·
                    refine ⟨56598877544035625566680341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37732585029357083711120227 56598877544035625566680341)
                    ·
                      refine ⟨2653072384876669948438141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56598877544035625566680341 2653072384876669948438141)
                      ·
                        rfl

theorem cell23_5166840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_5166840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166840 prefixEnd_5166840 := by exact prefixLift 5166840
  have htrace : WordTrace (prefixWord ++ tailWord_5166840) baseStart_5166840 baseEnd_5166840 := by
    simpa [prefixWord, tailWord_5166840, baseEnd_5166840] using wordTrace_append hprefix tailTrace_5166840
  have hstable : (prefixWord ++ tailWord_5166840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166840).length < 2 ^ (prefixWord ++ tailWord_5166840).sum := by decide
  have hdescent : baseEnd_5166840 < baseStart_5166840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166844 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_5166844 : Nat := 118140960795 + 5166844 * 2 ^ 59
def prefixEnd_5166844 : Nat := 4983230072969 + 3 ^ 40 * 5166844 * 2
def baseEnd_5166844 : Nat := 2653074438799287932788123

theorem tailTrace_5166844 : CollatzResearch.WordTrace tailWord_5166844 prefixEnd_5166844 2653074438799287932788123 := by
  unfold tailWord_5166844
  simp only [CollatzResearch.WordTrace]
  refine ⟨94225141246707044773365793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125633521662276059697821057 94225141246707044773365793)
  ·
    refine ⟨70668855935030283580024345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94225141246707044773365793 70668855935030283580024345)
    ·
      refine ⟨53001641951272712685018259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70668855935030283580024345 53001641951272712685018259)
      ·
        refine ⟨79502462926909069027527389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53001641951272712685018259 79502462926909069027527389)
        ·
          refine ⟨29813423597590900885322771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79502462926909069027527389 29813423597590900885322771)
          ·
            refine ⟨44720135396386351327984157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29813423597590900885322771 44720135396386351327984157)
            ·
              refine ⟨16770050773644881747994059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44720135396386351327984157 16770050773644881747994059)
              ·
                refine ⟨25155076160467322621991089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16770050773644881747994059 25155076160467322621991089)
                ·
                  refine ⟨18866307120350491966493317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25155076160467322621991089 18866307120350491966493317)
                  ·
                    refine ⟨3537432585065717243717497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18866307120350491966493317 3537432585065717243717497)
                    ·
                      refine ⟨2653074438799287932788123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537432585065717243717497 2653074438799287932788123)
                      ·
                        rfl

theorem cell23_5166844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_5166844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166844 prefixEnd_5166844 := by exact prefixLift 5166844
  have htrace : WordTrace (prefixWord ++ tailWord_5166844) baseStart_5166844 baseEnd_5166844 := by
    simpa [prefixWord, tailWord_5166844, baseEnd_5166844] using wordTrace_append hprefix tailTrace_5166844
  have hstable : (prefixWord ++ tailWord_5166844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166844).length < 2 ^ (prefixWord ++ tailWord_5166844).sum := by decide
  have hdescent : baseEnd_5166844 < baseStart_5166844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166847 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_5166847 : Nat := 118140960795 + 5166847 * 2 ^ 59
def prefixEnd_5166847 : Nat := 4983230072969 + 3 ^ 40 * 5166847 * 2
def baseEnd_5166847 : Nat := 2653075979241251421050609

theorem tailTrace_5166847 : CollatzResearch.WordTrace tailWord_5166847 prefixEnd_5166847 2653075979241251421050609 := by
  unfold tailWord_5166847
  simp only [CollatzResearch.WordTrace]
  refine ⟨188450391912403221059090795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125633594608268814039393863 188450391912403221059090795)
  ·
    refine ⟨282675587868604831588636193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188450391912403221059090795 282675587868604831588636193)
    ·
      refine ⟨212006690901453623691477145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282675587868604831588636193 212006690901453623691477145)
      ·
        refine ⟨159005018176090217768607859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212006690901453623691477145 159005018176090217768607859)
        ·
          refine ⟨238507527264135326652911789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159005018176090217768607859 238507527264135326652911789)
          ·
            refine ⟨89440322724050747494841921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238507527264135326652911789 89440322724050747494841921)
            ·
              refine ⟨67080242043038060621131441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89440322724050747494841921 67080242043038060621131441)
              ·
                refine ⟨50310181532278545465848581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67080242043038060621131441 50310181532278545465848581)
                ·
                  refine ⟨9433159037302227274846609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50310181532278545465848581 9433159037302227274846609)
                  ·
                    refine ⟨7074869277976670456134957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9433159037302227274846609 7074869277976670456134957)
                    ·
                      refine ⟨2653075979241251421050609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7074869277976670456134957 2653075979241251421050609)
                      ·
                        rfl

theorem cell23_5166847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_5166847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166847 prefixEnd_5166847 := by exact prefixLift 5166847
  have htrace : WordTrace (prefixWord ++ tailWord_5166847) baseStart_5166847 baseEnd_5166847 := by
    simpa [prefixWord, tailWord_5166847, baseEnd_5166847] using wordTrace_append hprefix tailTrace_5166847
  have hstable : (prefixWord ++ tailWord_5166847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166847).length < 2 ^ (prefixWord ++ tailWord_5166847).sum := by decide
  have hdescent : baseEnd_5166847 < baseStart_5166847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166871 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 1, 4]
def baseStart_5166871 : Nat := 118140960795 + 5166871 * 2 ^ 59
def prefixEnd_5166871 : Nat := 4983230072969 + 3 ^ 40 * 5166871 * 2
def baseEnd_5166871 : Nat := 884362767592319775716833

theorem tailTrace_5166871 : CollatzResearch.WordTrace tailWord_5166871 prefixEnd_5166871 884362767592319775716833 := by
  unfold tailWord_5166871
  simp only [CollatzResearch.WordTrace]
  refine ⟨188451267264316273157964467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125634178176210848771976311 188451267264316273157964467)
  ·
    refine ⟨282676900896474409736946701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188451267264316273157964467 282676900896474409736946701)
    ·
      refine ⟨106003837836177903651355013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282676900896474409736946701 106003837836177903651355013)
      ·
        refine ⟨19875719594283356934629065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106003837836177903651355013 19875719594283356934629065)
        ·
          refine ⟨14906789695712517700971799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19875719594283356934629065 14906789695712517700971799)
          ·
            refine ⟨22360184543568776551457699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14906789695712517700971799 22360184543568776551457699)
            ·
              refine ⟨33540276815353164827186549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22360184543568776551457699 33540276815353164827186549)
              ·
                refine ⟨3144400951439359202548739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33540276815353164827186549 3144400951439359202548739)
                ·
                  refine ⟨4716601427159038803823109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144400951439359202548739 4716601427159038803823109)
                  ·
                    refine ⟨884362767592319775716833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4716601427159038803823109 884362767592319775716833)
                    ·
                      rfl

theorem cell23_5166871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_5166871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166871 prefixEnd_5166871 := by exact prefixLift 5166871
  have htrace : WordTrace (prefixWord ++ tailWord_5166871) baseStart_5166871 baseEnd_5166871 := by
    simpa [prefixWord, tailWord_5166871, baseEnd_5166871] using wordTrace_append hprefix tailTrace_5166871
  have hstable : (prefixWord ++ tailWord_5166871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166871).length < 2 ^ (prefixWord ++ tailWord_5166871).sum := by decide
  have hdescent : baseEnd_5166871 < baseStart_5166871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166884 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 6]
def baseStart_5166884 : Nat := 118140960795 + 5166884 * 2 ^ 59
def prefixEnd_5166884 : Nat := 4983230072969 + 3 ^ 40 * 5166884 * 2
def baseEnd_5166884 : Nat := 294788330891718641809771

theorem tailTrace_5166884 : CollatzResearch.WordTrace tailWord_5166884 prefixEnd_5166884 294788330891718641809771 := by
  unfold tailWord_5166884
  simp only [CollatzResearch.WordTrace]
  refine ⟨94225870706634588189093853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125634494275512784252125137 94225870706634588189093853)
  ·
    refine ⟨35334701514987970570910195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94225870706634588189093853 35334701514987970570910195)
    ·
      refine ⟨53002052272481955856365293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35334701514987970570910195 53002052272481955856365293)
      ·
        refine ⟨19875769602180733446136985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53002052272481955856365293 19875769602180733446136985)
        ·
          refine ⟨14906827201635550084602739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19875769602180733446136985 14906827201635550084602739)
          ·
            refine ⟨22360240802453325126904109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14906827201635550084602739 22360240802453325126904109)
            ·
              refine ⟨8385090300919996922589041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22360240802453325126904109 8385090300919996922589041)
              ·
                refine ⟨6288817725689997691941781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8385090300919996922589041 6288817725689997691941781)
                ·
                  refine ⟨294788330891718641809771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6288817725689997691941781 294788330891718641809771)
                  ·
                    rfl

theorem cell23_5166884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_5166884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166884 prefixEnd_5166884 := by exact prefixLift 5166884
  have htrace : WordTrace (prefixWord ++ tailWord_5166884) baseStart_5166884 baseEnd_5166884 := by
    simpa [prefixWord, tailWord_5166884, baseEnd_5166884] using wordTrace_append hprefix tailTrace_5166884
  have hstable : (prefixWord ++ tailWord_5166884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166884).length < 2 ^ (prefixWord ++ tailWord_5166884).sum := by decide
  have hdescent : baseEnd_5166884 < baseStart_5166884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166901 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 6]
def baseStart_5166901 : Nat := 118140960795 + 5166901 * 2 ^ 59
def prefixEnd_5166901 : Nat := 4983230072969 + 3 ^ 40 * 5166901 * 2
def baseEnd_5166901 : Nat := 294789300799621578863929

theorem tailTrace_5166901 : CollatzResearch.WordTrace tailWord_5166901 prefixEnd_5166901 294789300799621578863929 := by
  unfold tailWord_5166901
  simp only [CollatzResearch.WordTrace]
  refine ⟨188452361454207588281556557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125634907636138392187704371 188452361454207588281556557)
  ·
    refine ⟨70669635545327845605583709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188452361454207588281556557 70669635545327845605583709)
    ·
      refine ⟨26501113329497942102093891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70669635545327845605583709 26501113329497942102093891)
      ·
        refine ⟨39751669994246913153140837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26501113329497942102093891 39751669994246913153140837)
        ·
          refine ⟨7453438123921296216213907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39751669994246913153140837 7453438123921296216213907)
          ·
            refine ⟨11180157185881944324320861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453438123921296216213907 11180157185881944324320861)
            ·
              refine ⟨4192558944705729121620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11180157185881944324320861 4192558944705729121620323)
              ·
                refine ⟨6288838417058593682430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192558944705729121620323 6288838417058593682430485)
                ·
                  refine ⟨294789300799621578863929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6288838417058593682430485 294789300799621578863929)
                  ·
                    rfl

theorem cell23_5166901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_5166901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166901 prefixEnd_5166901 := by exact prefixLift 5166901
  have htrace : WordTrace (prefixWord ++ tailWord_5166901) baseStart_5166901 baseEnd_5166901 := by
    simpa [prefixWord, tailWord_5166901, baseEnd_5166901] using wordTrace_append hprefix tailTrace_5166901
  have hstable : (prefixWord ++ tailWord_5166901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166901).length < 2 ^ (prefixWord ++ tailWord_5166901).sum := by decide
  have hdescent : baseEnd_5166901 < baseStart_5166901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166904 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_5166904 : Nat := 118140960795 + 5166904 * 2 ^ 59
def prefixEnd_5166904 : Nat := 4983230072969 + 3 ^ 40 * 5166904 * 2
def baseEnd_5166904 : Nat := 2653105247638557698037847

theorem tailTrace_5166904 : CollatzResearch.WordTrace tailWord_5166904 prefixEnd_5166904 2653105247638557698037847 := by
  unfold tailWord_5166904
  simp only [CollatzResearch.WordTrace]
  refine ⟨94226235436598359896957883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125634980582131146529277177 94226235436598359896957883)
  ·
    refine ⟨141339353154897539845436825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94226235436598359896957883 141339353154897539845436825)
    ·
      refine ⟨106004514866173154884077619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141339353154897539845436825 106004514866173154884077619)
      ·
        refine ⟨159006772299259732326116429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106004514866173154884077619 159006772299259732326116429)
        ·
          refine ⟨59627539612222399622293661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159006772299259732326116429 59627539612222399622293661)
          ·
            refine ⟨22360327354583399858360123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59627539612222399622293661 22360327354583399858360123)
            ·
              refine ⟨33540491031875099787540185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22360327354583399858360123 33540491031875099787540185)
              ·
                refine ⟨25155368273906324840655139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33540491031875099787540185 25155368273906324840655139)
                ·
                  refine ⟨37733052410859487260982709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25155368273906324840655139 37733052410859487260982709)
                  ·
                    refine ⟨3537473663518076930717129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37733052410859487260982709 3537473663518076930717129)
                    ·
                      refine ⟨2653105247638557698037847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537473663518076930717129 2653105247638557698037847)
                      ·
                        rfl

theorem cell23_5166904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_5166904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166904 prefixEnd_5166904 := by exact prefixLift 5166904
  have htrace : WordTrace (prefixWord ++ tailWord_5166904) baseStart_5166904 baseEnd_5166904 := by
    simpa [prefixWord, tailWord_5166904, baseEnd_5166904] using wordTrace_append hprefix tailTrace_5166904
  have hstable : (prefixWord ++ tailWord_5166904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166904).length < 2 ^ (prefixWord ++ tailWord_5166904).sum := by decide
  have hdescent : baseEnd_5166904 < baseStart_5166904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166944 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_5166944 : Nat := 118140960795 + 5166944 * 2 ^ 59
def prefixEnd_5166944 : Nat := 4983230072969 + 3 ^ 40 * 5166944 * 2
def baseEnd_5166944 : Nat := 884375262288245847179221

theorem tailTrace_5166944 : CollatzResearch.WordTrace tailWord_5166944 prefixEnd_5166944 884375262288245847179221 := by
  unfold tailWord_5166944
  simp only [CollatzResearch.WordTrace]
  refine ⟨94226964896525903312685943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125635953195367871083581257 94226964896525903312685943)
  ·
    refine ⟨141340447344788854969028915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94226964896525903312685943 141340447344788854969028915)
    ·
      refine ⟨212010671017183282453543373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141340447344788854969028915 212010671017183282453543373)
      ·
        refine ⟨79504001631443730920078765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212010671017183282453543373 79504001631443730920078765)
        ·
          refine ⟨29814000611791399095029537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79504001631443730920078765 29814000611791399095029537)
          ·
            refine ⟨22360500458843549321272153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29814000611791399095029537 22360500458843549321272153)
            ·
              refine ⟨16770375344132661990954115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22360500458843549321272153 16770375344132661990954115)
              ·
                refine ⟨25155563016198992986431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16770375344132661990954115 25155563016198992986431173)
                ·
                  refine ⟨4716668065537311184955845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25155563016198992986431173 4716668065537311184955845)
                  ·
                    refine ⟨884375262288245847179221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4716668065537311184955845 884375262288245847179221)
                    ·
                      rfl

theorem cell23_5166944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_5166944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166944 prefixEnd_5166944 := by exact prefixLift 5166944
  have htrace : WordTrace (prefixWord ++ tailWord_5166944) baseStart_5166944 baseEnd_5166944 := by
    simpa [prefixWord, tailWord_5166944, baseEnd_5166944] using wordTrace_append hprefix tailTrace_5166944
  have hstable : (prefixWord ++ tailWord_5166944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166944).length < 2 ^ (prefixWord ++ tailWord_5166944).sum := by decide
  have hdescent : baseEnd_5166944 < baseStart_5166944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166957 : List Nat := [1, 5, 1, 1, 1, 1, 3, 10]
def baseStart_5166957 : Nat := 118140960795 + 5166957 * 2 ^ 59
def prefixEnd_5166957 : Nat := 4983230072969 + 3 ^ 40 * 5166957 * 2
def baseEnd_5166957 : Nat := 98264165263453555210189

theorem tailTrace_5166957 : CollatzResearch.WordTrace tailWord_5166957 prefixEnd_5166957 98264165263453555210189 := by
  unfold tailWord_5166957
  simp only [CollatzResearch.WordTrace]
  refine ⟨188454403942004709845595125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125636269294669806563730083 188454403942004709845595125)
  ·
    refine ⟨17667600369562941548024543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188454403942004709845595125 17667600369562941548024543)
    ·
      refine ⟨26501400554344412322036815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17667600369562941548024543 26501400554344412322036815)
      ·
        refine ⟨39752100831516618483055223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26501400554344412322036815 39752100831516618483055223)
        ·
          refine ⟨59628151247274927724582835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39752100831516618483055223 59628151247274927724582835)
          ·
            refine ⟨89442226870912391586874253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59628151247274927724582835 89442226870912391586874253)
            ·
              refine ⟨33540835076592146845077845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89442226870912391586874253 33540835076592146845077845)
              ·
                refine ⟨98264165263453555210189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33540835076592146845077845 98264165263453555210189)
                ·
                  rfl

theorem cell23_5166957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 10].length) (baseStart_5166957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166957 prefixEnd_5166957 := by exact prefixLift 5166957
  have htrace : WordTrace (prefixWord ++ tailWord_5166957) baseStart_5166957 baseEnd_5166957 := by
    simpa [prefixWord, tailWord_5166957, baseEnd_5166957] using wordTrace_append hprefix tailTrace_5166957
  have hstable : (prefixWord ++ tailWord_5166957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166957).length < 2 ^ (prefixWord ++ tailWord_5166957).sum := by decide
  have hdescent : baseEnd_5166957 < baseStart_5166957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167001 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 3]
def baseStart_5167001 : Nat := 118140960795 + 5167001 * 2 ^ 59
def prefixEnd_5167001 : Nat := 4983230072969 + 3 ^ 40 * 5167001 * 2
def baseEnd_5167001 : Nat := 2653155055262043818524901

theorem tailTrace_5167001 : CollatzResearch.WordTrace tailWord_5167001 prefixEnd_5167001 2653155055262043818524901 := by
  unfold tailWord_5167001
  simp only [CollatzResearch.WordTrace]
  refine ⟨188456008753845305360196857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125637339169230203573464571 188456008753845305360196857)
  ·
    refine ⟨141342006565383979020147643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188456008753845305360196857 141342006565383979020147643)
    ·
      refine ⟨212013009848075968530221465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141342006565383979020147643 212013009848075968530221465)
      ·
        refine ⟨159009757386056976397666099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212013009848075968530221465 159009757386056976397666099)
        ·
          refine ⟨238514636079085464596499149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159009757386056976397666099 238514636079085464596499149)
          ·
            refine ⟨89442988529657049223687181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238514636079085464596499149 89442988529657049223687181)
            ·
              refine ⟨33541120698621393458882693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89442988529657049223687181 33541120698621393458882693)
              ·
                refine ⟨6288960130991511273540505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33541120698621393458882693 6288960130991511273540505)
                ·
                  refine ⟨4716720098243633455155379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6288960130991511273540505 4716720098243633455155379)
                  ·
                    refine ⟨7075080147365450182733069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4716720098243633455155379 7075080147365450182733069)
                    ·
                      refine ⟨2653155055262043818524901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075080147365450182733069 2653155055262043818524901)
                      ·
                        rfl

theorem cell23_5167001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_5167001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167001 prefixEnd_5167001 := by exact prefixLift 5167001
  have htrace : WordTrace (prefixWord ++ tailWord_5167001) baseStart_5167001 baseEnd_5167001 := by
    simpa [prefixWord, tailWord_5167001, baseEnd_5167001] using wordTrace_append hprefix tailTrace_5167001
  have hstable : (prefixWord ++ tailWord_5167001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167001).length < 2 ^ (prefixWord ++ tailWord_5167001).sum := by decide
  have hdescent : baseEnd_5167001 < baseStart_5167001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167002 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2]
def baseStart_5167002 : Nat := 118140960795 + 5167002 * 2 ^ 59
def prefixEnd_5167002 : Nat := 4983230072969 + 3 ^ 40 * 5167002 * 2
def baseEnd_5167002 : Nat := 2653155568742698314612397

theorem tailTrace_5167002 : CollatzResearch.WordTrace tailWord_5167002 prefixEnd_5167002 2653155568742698314612397 := by
  unfold tailWord_5167002
  simp only [CollatzResearch.WordTrace]
  refine ⟨47114011306710420632745815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125637363484561121687322173 47114011306710420632745815)
  ·
    refine ⟨70671016960065630949118723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47114011306710420632745815 70671016960065630949118723)
    ·
      refine ⟨106006525440098446423678085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70671016960065630949118723 106006525440098446423678085)
      ·
        refine ⟨19876223520018458704439641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106006525440098446423678085 19876223520018458704439641)
        ·
          refine ⟨14907167640013844028329731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19876223520018458704439641 14907167640013844028329731)
          ·
            refine ⟨22360751460020766042494597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14907167640013844028329731 22360751460020766042494597)
            ·
              refine ⟨4192640898753893632967737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22360751460020766042494597 4192640898753893632967737)
              ·
                refine ⟨3144480674065420224725803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192640898753893632967737 3144480674065420224725803)
                ·
                  refine ⟨4716721011098130337088705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144480674065420224725803 4716721011098130337088705)
                  ·
                    refine ⟨3537540758323597752816529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716721011098130337088705 3537540758323597752816529)
                    ·
                      refine ⟨2653155568742698314612397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537540758323597752816529 2653155568742698314612397)
                      ·
                        rfl

theorem cell23_5167002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_5167002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167002 prefixEnd_5167002 := by exact prefixLift 5167002
  have htrace : WordTrace (prefixWord ++ tailWord_5167002) baseStart_5167002 baseEnd_5167002 := by
    simpa [prefixWord, tailWord_5167002, baseEnd_5167002] using wordTrace_append hprefix tailTrace_5167002
  have hstable : (prefixWord ++ tailWord_5167002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167002).length < 2 ^ (prefixWord ++ tailWord_5167002).sum := by decide
  have hdescent : baseEnd_5167002 < baseStart_5167002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167004 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5167004 : Nat := 118140960795 + 5167004 * 2 ^ 59
def prefixEnd_5167004 : Nat := 4983230072969 + 3 ^ 40 * 5167004 * 2
def baseEnd_5167004 : Nat := 884385531901335768929129

theorem tailTrace_5167004 : CollatzResearch.WordTrace tailWord_5167004 prefixEnd_5167004 884385531901335768929129 := by
  unfold tailWord_5167004
  simp only [CollatzResearch.WordTrace]
  refine ⟨94228059086417218436278033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125637412115222957915037377 94228059086417218436278033)
  ·
    refine ⟨70671044314812913827208525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94228059086417218436278033 70671044314812913827208525)
    ·
      refine ⟨26501641618054842685203197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70671044314812913827208525 26501641618054842685203197)
      ·
        refine ⟨9938115606770566006951199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26501641618054842685203197 9938115606770566006951199)
        ·
          refine ⟨14907173410155849010426799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9938115606770566006951199 14907173410155849010426799)
          ·
            refine ⟨22360760115233773515640199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14907173410155849010426799 22360760115233773515640199)
            ·
              refine ⟨33541140172850660273460299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22360760115233773515640199 33541140172850660273460299)
              ·
                refine ⟨50311710259275990410190449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33541140172850660273460299 50311710259275990410190449)
                ·
                  refine ⟨37733782694456992807642837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50311710259275990410190449 37733782694456992807642837)
                  ·
                    refine ⟨884385531901335768929129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37733782694456992807642837 884385531901335768929129)
                    ·
                      rfl

theorem cell23_5167004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5167004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167004 prefixEnd_5167004 := by exact prefixLift 5167004
  have htrace : WordTrace (prefixWord ++ tailWord_5167004) baseStart_5167004 baseEnd_5167004 := by
    simpa [prefixWord, tailWord_5167004, baseEnd_5167004] using wordTrace_append hprefix tailTrace_5167004
  have hstable : (prefixWord ++ tailWord_5167004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167004).length < 2 ^ (prefixWord ++ tailWord_5167004).sum := by decide
  have hdescent : baseEnd_5167004 < baseStart_5167004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167047 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 11]
def baseStart_5167047 : Nat := 118140960795 + 5167047 * 2 ^ 59
def prefixEnd_5167047 : Nat := 4983230072969 + 3 ^ 40 * 5167047 * 2
def baseEnd_5167047 : Nat := 294797630596905626505521

theorem tailTrace_5167047 : CollatzResearch.WordTrace tailWord_5167047 prefixEnd_5167047 294797630596905626505521 := by
  unfold tailWord_5167047
  simp only [CollatzResearch.WordTrace]
  refine ⟨188457686511678655216371395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125638457674452436810914263 188457686511678655216371395)
  ·
    refine ⟨282686529767517982824557093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188457686511678655216371395 282686529767517982824557093)
    ·
      refine ⟨53003724331409621779604455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282686529767517982824557093 53003724331409621779604455)
      ·
        refine ⟨79505586497114432669406683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53003724331409621779604455 79505586497114432669406683)
        ·
          refine ⟨119258379745671649004110025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79505586497114432669406683 119258379745671649004110025)
          ·
            refine ⟨89443784809253736753082519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119258379745671649004110025 89443784809253736753082519)
            ·
              refine ⟨134165677213880605129623779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89443784809253736753082519 134165677213880605129623779)
              ·
                refine ⟨201248515820820907694435669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134165677213880605129623779 201248515820820907694435669)
                ·
                  refine ⟨294797630596905626505521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 201248515820820907694435669 294797630596905626505521)
                  ·
                    rfl

theorem cell23_5167047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 11].length) (baseStart_5167047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167047 prefixEnd_5167047 := by exact prefixLift 5167047
  have htrace : WordTrace (prefixWord ++ tailWord_5167047) baseStart_5167047 baseEnd_5167047 := by
    simpa [prefixWord, tailWord_5167047, baseEnd_5167047] using wordTrace_append hprefix tailTrace_5167047
  have hstable : (prefixWord ++ tailWord_5167047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167047).length < 2 ^ (prefixWord ++ tailWord_5167047).sum := by decide
  have hdescent : baseEnd_5167047 < baseStart_5167047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167054 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_5167054 : Nat := 118140960795 + 5167054 * 2 ^ 59
def prefixEnd_5167054 : Nat := 4983230072969 + 3 ^ 40 * 5167054 * 2
def baseEnd_5167054 : Nat := 2653182269736732111162157

theorem tailTrace_5167054 : CollatzResearch.WordTrace tailWord_5167054 prefixEnd_5167054 2653182269736732111162157 := by
  unfold tailWord_5167054
  simp only [CollatzResearch.WordTrace]
  refine ⟨23557242727831661926484527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125638627881768863607917477 23557242727831661926484527)
  ·
    refine ⟨35335864091747492889726791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23557242727831661926484527 35335864091747492889726791)
    ·
      refine ⟨53003796137621239334590187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35335864091747492889726791 53003796137621239334590187)
      ·
        refine ⟨79505694206431859001885281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53003796137621239334590187 79505694206431859001885281)
        ·
          refine ⟨59629270654823894251413961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79505694206431859001885281 59629270654823894251413961)
          ·
            refine ⟨44721952991117920688560471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59629270654823894251413961 44721952991117920688560471)
            ·
              refine ⟨67082929486676881032840707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44721952991117920688560471 67082929486676881032840707)
              ·
                refine ⟨100624394230015321549261061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67082929486676881032840707 100624394230015321549261061)
                ·
                  refine ⟨18867073918127872790486449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100624394230015321549261061 18867073918127872790486449)
                  ·
                    refine ⟨14150305438595904592864837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18867073918127872790486449 14150305438595904592864837)
                    ·
                      refine ⟨2653182269736732111162157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14150305438595904592864837 2653182269736732111162157)
                      ·
                        rfl

theorem cell23_5167054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_5167054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167054 prefixEnd_5167054 := by exact prefixLift 5167054
  have htrace : WordTrace (prefixWord ++ tailWord_5167054) baseStart_5167054 baseEnd_5167054 := by
    simpa [prefixWord, tailWord_5167054, baseEnd_5167054] using wordTrace_append hprefix tailTrace_5167054
  have hstable : (prefixWord ++ tailWord_5167054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167054).length < 2 ^ (prefixWord ++ tailWord_5167054).sum := by decide
  have hdescent : baseEnd_5167054 < baseStart_5167054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167057 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_5167057 : Nat := 118140960795 + 5167057 * 2 ^ 59
def prefixEnd_5167057 : Nat := 4983230072969 + 3 ^ 40 * 5167057 * 2
def baseEnd_5167057 : Nat := 2653183810178695599424643

theorem tailTrace_5167057 : CollatzResearch.WordTrace tailWord_5167057 prefixEnd_5167057 2653183810178695599424643 := by
  unfold tailWord_5167057
  simp only [CollatzResearch.WordTrace]
  refine ⟨188458051241642426924235425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125638700827761617949490283 188458051241642426924235425)
  ·
    refine ⟨141343538431231820193176569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188458051241642426924235425 141343538431231820193176569)
    ·
      refine ⟨106007653823423865144882427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141343538431231820193176569 106007653823423865144882427)
      ·
        refine ⟨159011480735135797717323641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106007653823423865144882427 159011480735135797717323641)
        ·
          refine ⟨119258610551351848287992731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159011480735135797717323641 119258610551351848287992731)
          ·
            refine ⟨178887915827027772431989097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119258610551351848287992731 178887915827027772431989097)
            ·
              refine ⟨134165936870270829323991823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178887915827027772431989097 134165936870270829323991823)
              ·
                refine ⟨201248905305406243985987735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134165936870270829323991823 201248905305406243985987735)
                ·
                  refine ⟨301873357958109365978981603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201248905305406243985987735 301873357958109365978981603)
                  ·
                    refine ⟨452810036937164048968472405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 301873357958109365978981603 452810036937164048968472405)
                    ·
                      refine ⟨2653183810178695599424643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 452810036937164048968472405 2653183810178695599424643)
                      ·
                        rfl

theorem cell23_5167057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_5167057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167057 prefixEnd_5167057 := by exact prefixLift 5167057
  have htrace : WordTrace (prefixWord ++ tailWord_5167057) baseStart_5167057 baseEnd_5167057 := by
    simpa [prefixWord, tailWord_5167057, baseEnd_5167057] using wordTrace_append hprefix tailTrace_5167057
  have hstable : (prefixWord ++ tailWord_5167057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167057).length < 2 ^ (prefixWord ++ tailWord_5167057).sum := by decide
  have hdescent : baseEnd_5167057 < baseStart_5167057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167064 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 7]
def baseStart_5167064 : Nat := 118140960795 + 5167064 * 2 ^ 59
def prefixEnd_5167064 : Nat := 4983230072969 + 3 ^ 40 * 5167064 * 2
def baseEnd_5167064 : Nat := 294798600504808563559679

theorem tailTrace_5167064 : CollatzResearch.WordTrace tailWord_5167064 prefixEnd_5167064 294798600504808563559679 := by
  unfold tailWord_5167064
  simp only [CollatzResearch.WordTrace]
  refine ⟨94229153276308533559870123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125638871035078044746493497 94229153276308533559870123)
  ·
    refine ⟨141343729914462800339805185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94229153276308533559870123 141343729914462800339805185)
    ·
      refine ⟨106007797435847100254853889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141343729914462800339805185 106007797435847100254853889)
      ·
        refine ⟨79505848076885325191140417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106007797435847100254853889 79505848076885325191140417)
        ·
          refine ⟨59629386057663993893355313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79505848076885325191140417 59629386057663993893355313)
          ·
            refine ⟨44722039543247995420016485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59629386057663993893355313 44722039543247995420016485)
            ·
              refine ⟨8385382414358999141253091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44722039543247995420016485 8385382414358999141253091)
              ·
                refine ⟨12578073621538498711879637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8385382414358999141253091 12578073621538498711879637)
                ·
                  refine ⟨294798600504808563559679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12578073621538498711879637 294798600504808563559679)
                  ·
                    rfl

theorem cell23_5167064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_5167064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167064 prefixEnd_5167064 := by exact prefixLift 5167064
  have htrace : WordTrace (prefixWord ++ tailWord_5167064) baseStart_5167064 baseEnd_5167064 := by
    simpa [prefixWord, tailWord_5167064, baseEnd_5167064] using wordTrace_append hprefix tailTrace_5167064
  have hstable : (prefixWord ++ tailWord_5167064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167064).length < 2 ^ (prefixWord ++ tailWord_5167064).sum := by decide
  have hdescent : baseEnd_5167064 < baseStart_5167064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167111 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 2, 5]
def baseStart_5167111 : Nat := 118140960795 + 5167111 * 2 ^ 59
def prefixEnd_5167111 : Nat := 4983230072969 + 3 ^ 40 * 5167111 * 2
def baseEnd_5167111 : Nat := 884403846044679462716465

theorem tailTrace_5167111 : CollatzResearch.WordTrace tailWord_5167111 prefixEnd_5167111 884403846044679462716465 := by
  unfold tailWord_5167111
  simp only [CollatzResearch.WordTrace]
  refine ⟨188460020783446794146701187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125640013855631196097800791 188460020783446794146701187)
  ·
    refine ⟨282690031175170191220051781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188460020783446794146701187 282690031175170191220051781)
    ·
      refine ⟨53004380845344410853759709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282690031175170191220051781 53004380845344410853759709)
      ·
        refine ⟨19876642817004154070159891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53004380845344410853759709 19876642817004154070159891)
        ·
          refine ⟨29814964225506231105239837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19876642817004154070159891 29814964225506231105239837)
          ·
            refine ⟨11180611584564836664464939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29814964225506231105239837 11180611584564836664464939)
            ·
              refine ⟨16770917376847254996697409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180611584564836664464939 16770917376847254996697409)
              ·
                refine ⟨12578188032635441247523057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16770917376847254996697409 12578188032635441247523057)
                ·
                  refine ⟨9433641024476580935642293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12578188032635441247523057 9433641024476580935642293)
                  ·
                    refine ⟨884403846044679462716465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433641024476580935642293 884403846044679462716465)
                    ·
                      rfl

theorem cell23_5167111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_5167111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167111 prefixEnd_5167111 := by exact prefixLift 5167111
  have htrace : WordTrace (prefixWord ++ tailWord_5167111) baseStart_5167111 baseEnd_5167111 := by
    simpa [prefixWord, tailWord_5167111, baseEnd_5167111] using wordTrace_append hprefix tailTrace_5167111
  have hstable : (prefixWord ++ tailWord_5167111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167111).length < 2 ^ (prefixWord ++ tailWord_5167111).sum := by decide
  have hdescent : baseEnd_5167111 < baseStart_5167111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167194 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_5167194 : Nat := 118140960795 + 5167194 * 2 ^ 59
def prefixEnd_5167194 : Nat := 4983230072969 + 3 ^ 40 * 5167194 * 2
def baseEnd_5167194 : Nat := 2653254157028361563411513

theorem tailTrace_5167194 : CollatzResearch.WordTrace tailWord_5167194 prefixEnd_5167194 2653254157028361563411513 := by
  unfold tailWord_5167194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47115762010536524830493159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125642032028097399547981757 47115762010536524830493159)
  ·
    refine ⟨70673643015804787245739739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47115762010536524830493159 70673643015804787245739739)
    ·
      refine ⟨106010464523707180868609609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70673643015804787245739739 106010464523707180868609609)
      ·
        refine ⟨79507848392780385651457207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106010464523707180868609609 79507848392780385651457207)
        ·
          refine ⟨119261772589170578477185811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79507848392780385651457207 119261772589170578477185811)
          ·
            refine ⟨178892658883755867715778717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119261772589170578477185811 178892658883755867715778717)
            ·
              refine ⟨67084747081408450393417019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178892658883755867715778717 67084747081408450393417019)
              ·
                refine ⟨100627120622112675590125529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67084747081408450393417019 100627120622112675590125529)
                ·
                  refine ⟨75470340466584506692594147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100627120622112675590125529 75470340466584506692594147)
                  ·
                    refine ⟨113205510699876760038891221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75470340466584506692594147 113205510699876760038891221)
                    ·
                      refine ⟨2653254157028361563411513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113205510699876760038891221 2653254157028361563411513)
                      ·
                        rfl

theorem cell23_5167194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_5167194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167194 prefixEnd_5167194 := by exact prefixLift 5167194
  have htrace : WordTrace (prefixWord ++ tailWord_5167194) baseStart_5167194 baseEnd_5167194 := by
    simpa [prefixWord, tailWord_5167194, baseEnd_5167194] using wordTrace_append hprefix tailTrace_5167194
  have hstable : (prefixWord ++ tailWord_5167194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167194).length < 2 ^ (prefixWord ++ tailWord_5167194).sum := by decide
  have hdescent : baseEnd_5167194 < baseStart_5167194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167201 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_5167201 : Nat := 118140960795 + 5167201 * 2 ^ 59
def prefixEnd_5167201 : Nat := 4983230072969 + 3 ^ 40 * 5167201 * 2
def baseEnd_5167201 : Nat := 884419250464314345341327

theorem tailTrace_5167201 : CollatzResearch.WordTrace tailWord_5167201 prefixEnd_5167201 884419250464314345341327 := by
  unfold tailWord_5167201
  simp only [CollatzResearch.WordTrace]
  refine ⟨188463303353120739517477457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125642202235413826344984971 188463303353120739517477457)
  ·
    refine ⟨141347477514840554638108093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188463303353120739517477457 141347477514840554638108093)
    ·
      refine ⟨53005304068065207989290535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141347477514840554638108093 53005304068065207989290535)
      ·
        refine ⟨79507956102097811983935803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53005304068065207989290535 79507956102097811983935803)
        ·
          refine ⟨119261934153146717975903705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79507956102097811983935803 119261934153146717975903705)
          ·
            refine ⟨89446450614860038481927779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119261934153146717975903705 89446450614860038481927779)
            ·
              refine ⟨134169675922290057722891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89446450614860038481927779 134169675922290057722891669)
              ·
                refine ⟨6289203558857346455760547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134169675922290057722891669 6289203558857346455760547)
                ·
                  refine ⟨9433805338286019683640821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289203558857346455760547 9433805338286019683640821)
                  ·
                    refine ⟨884419250464314345341327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433805338286019683640821 884419250464314345341327)
                    ·
                      rfl

theorem cell23_5167201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_5167201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167201 prefixEnd_5167201 := by exact prefixLift 5167201
  have htrace : WordTrace (prefixWord ++ tailWord_5167201) baseStart_5167201 baseEnd_5167201 := by
    simpa [prefixWord, tailWord_5167201, baseEnd_5167201] using wordTrace_append hprefix tailTrace_5167201
  have hstable : (prefixWord ++ tailWord_5167201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167201).length < 2 ^ (prefixWord ++ tailWord_5167201).sum := by decide
  have hdescent : baseEnd_5167201 < baseStart_5167201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167202 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5167202 : Nat := 118140960795 + 5167202 * 2 ^ 59
def prefixEnd_5167202 : Nat := 4983230072969 + 3 ^ 40 * 5167202 * 2
def baseEnd_5167202 : Nat := 2653258264873597532111477

theorem tailTrace_5167202 : CollatzResearch.WordTrace tailWord_5167202 prefixEnd_5167202 2653258264873597532111477 := by
  unfold tailWord_5167202
  simp only [CollatzResearch.WordTrace]
  refine ⟨47115834956529279172065965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125642226550744744458842573 47115834956529279172065965)
  ·
    refine ⟨17668438108698479689524737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47115834956529279172065965 17668438108698479689524737)
    ·
      refine ⟨13251328581523859767143553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17668438108698479689524737 13251328581523859767143553)
      ·
        refine ⟨9938496436142894825357665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13251328581523859767143553 9938496436142894825357665)
        ·
          refine ⟨7453872327107171119018249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9938496436142894825357665 7453872327107171119018249)
          ·
            refine ⟨5590404245330378339263687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7453872327107171119018249 5590404245330378339263687)
            ·
              refine ⟨8385606367995567508895531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590404245330378339263687 8385606367995567508895531)
              ·
                refine ⟨12578409551993351263343297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8385606367995567508895531 12578409551993351263343297)
                ·
                  refine ⟨9433807163995013447507473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12578409551993351263343297 9433807163995013447507473)
                  ·
                    refine ⟨7075355372996260085630605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9433807163995013447507473 7075355372996260085630605)
                    ·
                      refine ⟨2653258264873597532111477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075355372996260085630605 2653258264873597532111477)
                      ·
                        rfl

theorem cell23_5167202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5167202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167202 prefixEnd_5167202 := by exact prefixLift 5167202
  have htrace : WordTrace (prefixWord ++ tailWord_5167202) baseStart_5167202 baseEnd_5167202 := by
    simpa [prefixWord, tailWord_5167202, baseEnd_5167202] using wordTrace_append hprefix tailTrace_5167202
  have hstable : (prefixWord ++ tailWord_5167202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167202).length < 2 ^ (prefixWord ++ tailWord_5167202).sum := by decide
  have hdescent : baseEnd_5167202 < baseStart_5167202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167215 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 1, 1, 3]
def baseStart_5167215 : Nat := 118140960795 + 5167215 * 2 ^ 59
def prefixEnd_5167215 : Nat := 4983230072969 + 3 ^ 40 * 5167215 * 2
def baseEnd_5167215 : Nat := 2653264940122105981248917

theorem tailTrace_5167215 : CollatzResearch.WordTrace tailWord_5167215 prefixEnd_5167215 2653264940122105981248917 := by
  unfold tailWord_5167215
  simp only [CollatzResearch.WordTrace]
  refine ⟨188463813975070019908487099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125642542650046679938991399 188463813975070019908487099)
  ·
    refine ⟨282695720962605029862730649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188463813975070019908487099 282695720962605029862730649)
    ·
      refine ⟨212021790721953772397047987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282695720962605029862730649 212021790721953772397047987)
      ·
        refine ⟨318032686082930658595571981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212021790721953772397047987 318032686082930658595571981)
        ·
          refine ⟨119262257281098996973339493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318032686082930658595571981 119262257281098996973339493)
          ·
            refine ⟨22361673240206061932501155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119262257281098996973339493 22361673240206061932501155)
            ·
              refine ⟨33542509860309092898751733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22361673240206061932501155 33542509860309092898751733)
              ·
                refine ⟨3144610299403977459257975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33542509860309092898751733 3144610299403977459257975)
                ·
                  refine ⟨4716915449105966188886963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144610299403977459257975 4716915449105966188886963)
                  ·
                    refine ⟨7075373173658949283330445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4716915449105966188886963 7075373173658949283330445)
                    ·
                      refine ⟨2653264940122105981248917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075373173658949283330445 2653264940122105981248917)
                      ·
                        rfl

theorem cell23_5167215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 1, 3].length) (baseStart_5167215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167215 prefixEnd_5167215 := by exact prefixLift 5167215
  have htrace : WordTrace (prefixWord ++ tailWord_5167215) baseStart_5167215 baseEnd_5167215 := by
    simpa [prefixWord, tailWord_5167215, baseEnd_5167215] using wordTrace_append hprefix tailTrace_5167215
  have hstable : (prefixWord ++ tailWord_5167215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167215).length < 2 ^ (prefixWord ++ tailWord_5167215).sum := by decide
  have hdescent : baseEnd_5167215 < baseStart_5167215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167218 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_5167218 : Nat := 118140960795 + 5167218 * 2 ^ 59
def prefixEnd_5167218 : Nat := 4983230072969 + 3 ^ 40 * 5167218 * 2
def baseEnd_5167218 : Nat := 884422160188023156503801

theorem tailTrace_5167218 : CollatzResearch.WordTrace tailWord_5167218 prefixEnd_5167218 884422160188023156503801 := by
  unfold tailWord_5167218
  simp only [CollatzResearch.WordTrace]
  refine ⟨47115980848514787855211577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125642615596039434280564205 47115980848514787855211577)
  ·
    refine ⟨35336985636386090891408683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47115980848514787855211577 35336985636386090891408683)
    ·
      refine ⟨53005478454579136337113025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35336985636386090891408683 53005478454579136337113025)
      ·
        refine ⟨39754108840934352252834769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53005478454579136337113025 39754108840934352252834769)
        ·
          refine ⟨29815581630700764189626077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39754108840934352252834769 29815581630700764189626077)
          ·
            refine ⟨11180843111512786571109779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29815581630700764189626077 11180843111512786571109779)
            ·
              refine ⟨16771264667269179856664669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180843111512786571109779 16771264667269179856664669)
              ·
                refine ⟨6289224250225942446249251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16771264667269179856664669 6289224250225942446249251)
                ·
                  refine ⟨9433836375338913669373877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289224250225942446249251 9433836375338913669373877)
                  ·
                    refine ⟨884422160188023156503801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433836375338913669373877 884422160188023156503801)
                    ·
                      rfl

theorem cell23_5167218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_5167218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167218 prefixEnd_5167218 := by exact prefixLift 5167218
  have htrace : WordTrace (prefixWord ++ tailWord_5167218) baseStart_5167218 baseEnd_5167218 := by
    simpa [prefixWord, tailWord_5167218, baseEnd_5167218] using wordTrace_append hprefix tailTrace_5167218
  have hstable : (prefixWord ++ tailWord_5167218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167218).length < 2 ^ (prefixWord ++ tailWord_5167218).sum := by decide
  have hdescent : baseEnd_5167218 < baseStart_5167218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167241 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_5167241 : Nat := 118140960795 + 5167241 * 2 ^ 59
def prefixEnd_5167241 : Nat := 4983230072969 + 3 ^ 40 * 5167241 * 2
def baseEnd_5167241 : Nat := 2653278290619122879523797

theorem tailTrace_5167241 : CollatzResearch.WordTrace tailWord_5167241 prefixEnd_5167241 2653278290619122879523797 := by
  unfold tailWord_5167241
  simp only [CollatzResearch.WordTrace]
  refine ⟨188464762272975826348933577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125643174848650550899289051 188464762272975826348933577)
  ·
    refine ⟨141348571704731869761700183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188464762272975826348933577 141348571704731869761700183)
    ·
      refine ⟨212022857557097804642550275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141348571704731869761700183 212022857557097804642550275)
      ·
        refine ⟨318034286335646706963825413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212022857557097804642550275 318034286335646706963825413)
        ·
          refine ⟨59631428687933757555717265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318034286335646706963825413 59631428687933757555717265)
          ·
            refine ⟨44723571515950318166787949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59631428687933757555717265 44723571515950318166787949)
            ·
              refine ⟨16771339318481369312545481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44723571515950318166787949 16771339318481369312545481)
              ·
                refine ⟨12578504488861026984409111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16771339318481369312545481 12578504488861026984409111)
                ·
                  refine ⟨18867756733291540476613667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12578504488861026984409111 18867756733291540476613667)
                  ·
                    refine ⟨28301635099937310714920501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18867756733291540476613667 28301635099937310714920501)
                    ·
                      refine ⟨2653278290619122879523797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28301635099937310714920501 2653278290619122879523797)
                      ·
                        rfl

theorem cell23_5167241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_5167241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167241 prefixEnd_5167241 := by exact prefixLift 5167241
  have htrace : WordTrace (prefixWord ++ tailWord_5167241) baseStart_5167241 baseEnd_5167241 := by
    simpa [prefixWord, tailWord_5167241, baseEnd_5167241] using wordTrace_append hprefix tailTrace_5167241
  have hstable : (prefixWord ++ tailWord_5167241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167241).length < 2 ^ (prefixWord ++ tailWord_5167241).sum := by decide
  have hdescent : baseEnd_5167241 < baseStart_5167241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167252 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_5167252 : Nat := 118140960795 + 5167252 * 2 ^ 59
def prefixEnd_5167252 : Nat := 4983230072969 + 3 ^ 40 * 5167252 * 2
def baseEnd_5167252 : Nat := 884427979635440778828749

theorem tailTrace_5167252 : CollatzResearch.WordTrace tailWord_5167252 prefixEnd_5167252 884427979635440778828749 := by
  unfold tailWord_5167252
  simp only [CollatzResearch.WordTrace]
  refine ⟨94232581737967987613792005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125643442317290650151722673 94232581737967987613792005)
  ·
    refine ⟨17668609075868997677586001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94232581737967987613792005 17668609075868997677586001)
    ·
      refine ⟨13251456806901748258189501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17668609075868997677586001 13251456806901748258189501)
      ·
        refine ⟨4969296302588155596821063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13251456806901748258189501 4969296302588155596821063)
        ·
          refine ⟨7453944453882233395231595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969296302588155596821063 7453944453882233395231595)
          ·
            refine ⟨11180916680823350092847393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453944453882233395231595 11180916680823350092847393)
            ·
              refine ⟨8385687510617512569635545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11180916680823350092847393 8385687510617512569635545)
              ·
                refine ⟨6289265632963134427226659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8385687510617512569635545 6289265632963134427226659)
                ·
                  refine ⟨9433898449444701640839989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289265632963134427226659 9433898449444701640839989)
                  ·
                    refine ⟨884427979635440778828749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433898449444701640839989 884427979635440778828749)
                    ·
                      rfl

theorem cell23_5167252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_5167252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167252 prefixEnd_5167252 := by exact prefixLift 5167252
  have htrace : WordTrace (prefixWord ++ tailWord_5167252) baseStart_5167252 baseEnd_5167252 := by
    simpa [prefixWord, tailWord_5167252, baseEnd_5167252] using wordTrace_append hprefix tailTrace_5167252
  have hstable : (prefixWord ++ tailWord_5167252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167252).length < 2 ^ (prefixWord ++ tailWord_5167252).sum := by decide
  have hdescent : baseEnd_5167252 < baseStart_5167252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167255 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_5167255 : Nat := 118140960795 + 5167255 * 2 ^ 59
def prefixEnd_5167255 : Nat := 4983230072969 + 3 ^ 40 * 5167255 * 2
def baseEnd_5167255 : Nat := 2653285479348285824748733

theorem tailTrace_5167255 : CollatzResearch.WordTrace tailWord_5167255 prefixEnd_5167255 2653285479348285824748733 := by
  unfold tailWord_5167255
  simp only [CollatzResearch.WordTrace]
  refine ⟨188465272894925106739943219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125643515263283404493295479 188465272894925106739943219)
  ·
    refine ⟨282697909342387660109914829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188465272894925106739943219 282697909342387660109914829)
    ·
      refine ⟨106011716003395372541218061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282697909342387660109914829 106011716003395372541218061)
      ·
        refine ⟨39754393501273264702956773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106011716003395372541218061 39754393501273264702956773)
        ·
          refine ⟨7453948781488737131804395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39754393501273264702956773 7453948781488737131804395)
          ·
            refine ⟨11180923172233105697706593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453948781488737131804395 11180923172233105697706593)
            ·
              refine ⟨8385692379174829273279945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11180923172233105697706593 8385692379174829273279945)
              ·
                refine ⟨6289269284381121954959959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8385692379174829273279945 6289269284381121954959959)
                ·
                  refine ⟨9433903926571682932439939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289269284381121954959959 9433903926571682932439939)
                  ·
                    refine ⟨14150855889857524398659909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9433903926571682932439939 14150855889857524398659909)
                    ·
                      refine ⟨2653285479348285824748733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14150855889857524398659909 2653285479348285824748733)
                      ·
                        rfl

theorem cell23_5167255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_5167255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167255 prefixEnd_5167255 := by exact prefixLift 5167255
  have htrace : WordTrace (prefixWord ++ tailWord_5167255) baseStart_5167255 baseEnd_5167255 := by
    simpa [prefixWord, tailWord_5167255, baseEnd_5167255] using wordTrace_append hprefix tailTrace_5167255
  have hstable : (prefixWord ++ tailWord_5167255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167255).length < 2 ^ (prefixWord ++ tailWord_5167255).sum := by decide
  have hdescent : baseEnd_5167255 < baseStart_5167255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167261 : List Nat := [1, 4, 2, 1, 1, 4, 1, 9]
def baseStart_5167261 : Nat := 118140960795 + 5167261 * 2 ^ 59
def prefixEnd_5167261 : Nat := 4983230072969 + 3 ^ 40 * 5167261 * 2
def baseEnd_5167261 : Nat := 98269946675267140787915

theorem tailTrace_5167261 : CollatzResearch.WordTrace tailWord_5167261 prefixEnd_5167261 98269946675267140787915 := by
  unfold tailWord_5167261
  simp only [CollatzResearch.WordTrace]
  refine ⟨188465491732903369764661637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125643661155268913176441091 188465491732903369764661637)
  ·
    refine ⟨35337279699919381830874057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188465491732903369764661637 35337279699919381830874057)
    ·
      refine ⟨26502959774939536373155543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35337279699919381830874057 26502959774939536373155543)
      ·
        refine ⟨39754439662409304559733315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26502959774939536373155543 39754439662409304559733315)
        ·
          refine ⟨59631659493613956839599973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39754439662409304559733315 59631659493613956839599973)
          ·
            refine ⟨11180936155052616907424995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59631659493613956839599973 11180936155052616907424995)
            ·
              refine ⟨16771404232578925361137493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180936155052616907424995 16771404232578925361137493)
              ·
                refine ⟨98269946675267140787915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16771404232578925361137493 98269946675267140787915)
                ·
                  rfl

theorem cell23_5167261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 9].length) (baseStart_5167261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167261 prefixEnd_5167261 := by exact prefixLift 5167261
  have htrace : WordTrace (prefixWord ++ tailWord_5167261) baseStart_5167261 baseEnd_5167261 := by
    simpa [prefixWord, tailWord_5167261, baseEnd_5167261] using wordTrace_append hprefix tailTrace_5167261
  have hstable : (prefixWord ++ tailWord_5167261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167261).length < 2 ^ (prefixWord ++ tailWord_5167261).sum := by decide
  have hdescent : baseEnd_5167261 < baseStart_5167261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167288 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_5167288 : Nat := 118140960795 + 5167288 * 2 ^ 59
def prefixEnd_5167288 : Nat := 4983230072969 + 3 ^ 40 * 5167288 * 2
def baseEnd_5167288 : Nat := 2653302424209884195636081

theorem tailTrace_5167288 : CollatzResearch.WordTrace tailWord_5167288 prefixEnd_5167288 2653302424209884195636081 := by
  unfold tailWord_5167288
  simp only [CollatzResearch.WordTrace]
  refine ⟨94233238251902776687947259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125644317669203702250596345 94233238251902776687947259)
  ·
    refine ⟨141349857377854165031920889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94233238251902776687947259 141349857377854165031920889)
    ·
      refine ⟨106012393033390623773940667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141349857377854165031920889 106012393033390623773940667)
      ·
        refine ⟨159018589550085935660911001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106012393033390623773940667 159018589550085935660911001)
        ·
          refine ⟨119263942162564451745683251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159018589550085935660911001 119263942162564451745683251)
          ·
            refine ⟨178895913243846677618524877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119263942162564451745683251 178895913243846677618524877)
            ·
              refine ⟨67085967466442504106946829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178895913243846677618524877 67085967466442504106946829)
              ·
                refine ⟨25157237799915939040105061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67085967466442504106946829 25157237799915939040105061)
                ·
                  refine ⟨4716982087484238570019699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25157237799915939040105061 4716982087484238570019699)
                  ·
                    refine ⟨7075473131226357855029549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4716982087484238570019699 7075473131226357855029549)
                    ·
                      refine ⟨2653302424209884195636081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075473131226357855029549 2653302424209884195636081)
                      ·
                        rfl

theorem cell23_5167288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_5167288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167288 prefixEnd_5167288 := by exact prefixLift 5167288
  have htrace : WordTrace (prefixWord ++ tailWord_5167288) baseStart_5167288 baseEnd_5167288 := by
    simpa [prefixWord, tailWord_5167288, baseEnd_5167288] using wordTrace_append hprefix tailTrace_5167288
  have hstable : (prefixWord ++ tailWord_5167288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167288).length < 2 ^ (prefixWord ++ tailWord_5167288).sum := by decide
  have hdescent : baseEnd_5167288 < baseStart_5167288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167289 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5167289 : Nat := 118140960795 + 5167289 * 2 ^ 59
def prefixEnd_5167289 : Nat := 4983230072969 + 3 ^ 40 * 5167289 * 2
def baseEnd_5167289 : Nat := 2653302937690538691723577

theorem tailTrace_5167289 : CollatzResearch.WordTrace tailWord_5167289 prefixEnd_5167289 2653302937690538691723577 := by
  unfold tailWord_5167289
  simp only [CollatzResearch.WordTrace]
  refine ⟨188466512976801930546680921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125644341984534620364453947 188466512976801930546680921)
  ·
    refine ⟨141349884732601447910010691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188466512976801930546680921 141349884732601447910010691)
    ·
      refine ⟨212024827098902171865016037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141349884732601447910010691 212024827098902171865016037)
      ·
        refine ⟨39754655081044157224690507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212024827098902171865016037 39754655081044157224690507)
        ·
          refine ⟨59631982621566235837035761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39754655081044157224690507 59631982621566235837035761)
          ·
            refine ⟨44723986966174676877776821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59631982621566235837035761 44723986966174676877776821)
            ·
              refine ⟨4192873778078875957291577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44723986966174676877776821 4192873778078875957291577)
              ·
                refine ⟨3144655333559156967968683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192873778078875957291577 3144655333559156967968683)
                ·
                  refine ⟨4716983000338735451953025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144655333559156967968683 4716983000338735451953025)
                  ·
                    refine ⟨3537737250254051588964769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716983000338735451953025 3537737250254051588964769)
                    ·
                      refine ⟨2653302937690538691723577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537737250254051588964769 2653302937690538691723577)
                      ·
                        rfl

theorem cell23_5167289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5167289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167289 prefixEnd_5167289 := by exact prefixLift 5167289
  have htrace : WordTrace (prefixWord ++ tailWord_5167289) baseStart_5167289 baseEnd_5167289 := by
    simpa [prefixWord, tailWord_5167289, baseEnd_5167289] using wordTrace_append hprefix tailTrace_5167289
  have hstable : (prefixWord ++ tailWord_5167289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167289).length < 2 ^ (prefixWord ++ tailWord_5167289).sum := by decide
  have hdescent : baseEnd_5167289 < baseStart_5167289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167345 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_5167345 : Nat := 118140960795 + 5167345 * 2 ^ 59
def prefixEnd_5167345 : Nat := 4983230072969 + 3 ^ 40 * 5167345 * 2
def baseEnd_5167345 : Nat := 2653331692607190472623319

theorem tailTrace_5167345 : CollatzResearch.WordTrace tailWord_5167345 prefixEnd_5167345 2653331692607190472623319 := by
  unfold tailWord_5167345
  simp only [CollatzResearch.WordTrace]
  refine ⟨188468555464599052110719489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125645703643066034740479659 188468555464599052110719489)
  ·
    refine ⟨141351416598449289083039617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188468555464599052110719489 141351416598449289083039617)
    ·
      refine ⟨106013562448836966812279713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141351416598449289083039617 106013562448836966812279713)
      ·
        refine ⟨79510171836627725109209785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106013562448836966812279713 79510171836627725109209785)
        ·
          refine ⟨59632628877470793831907339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79510171836627725109209785 59632628877470793831907339)
          ·
            refine ⟨89448943316206190747861009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59632628877470793831907339 89448943316206190747861009)
            ·
              refine ⟨67086707487154643060895757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89448943316206190747861009 67086707487154643060895757)
              ·
                refine ⟨25157515307682991147835909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67086707487154643060895757 25157515307682991147835909)
                ·
                  refine ⟨4717034120190560840219233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25157515307682991147835909 4717034120190560840219233)
                  ·
                    refine ⟨3537775590142920630164425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4717034120190560840219233 3537775590142920630164425)
                    ·
                      refine ⟨2653331692607190472623319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537775590142920630164425 2653331692607190472623319)
                      ·
                        rfl

theorem cell23_5167345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_5167345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167345 prefixEnd_5167345 := by exact prefixLift 5167345
  have htrace : WordTrace (prefixWord ++ tailWord_5167345) baseStart_5167345 baseEnd_5167345 := by
    simpa [prefixWord, tailWord_5167345, baseEnd_5167345] using wordTrace_append hprefix tailTrace_5167345
  have hstable : (prefixWord ++ tailWord_5167345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167345).length < 2 ^ (prefixWord ++ tailWord_5167345).sum := by decide
  have hdescent : baseEnd_5167345 < baseStart_5167345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167362 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5167362 : Nat := 118140960795 + 5167362 * 2 ^ 59
def prefixEnd_5167362 : Nat := 4983230072969 + 3 ^ 40 * 5167362 * 2
def baseEnd_5167362 : Nat := 2653340421778316906110741

theorem tailTrace_5167362 : CollatzResearch.WordTrace tailWord_5167362 prefixEnd_5167362 2653340421778316906110741 := by
  unfold tailWord_5167362
  simp only [CollatzResearch.WordTrace]
  refine ⟨47117293876384366003522085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125646117003691642676058893 47117293876384366003522085)
  ·
    refine ⟨8834492601822068625660391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47117293876384366003522085 8834492601822068625660391)
    ·
      refine ⟨13251738902733102938490587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8834492601822068625660391 13251738902733102938490587)
      ·
        refine ⟨19877608354099654407735881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13251738902733102938490587 19877608354099654407735881)
        ·
          refine ⟨14908206265574740805801911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19877608354099654407735881 14908206265574740805801911)
          ·
            refine ⟨22362309398362111208702867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14908206265574740805801911 22362309398362111208702867)
            ·
              refine ⟨33543464097543166813054301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22362309398362111208702867 33543464097543166813054301)
              ·
                refine ⟨12578799036578687554895363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33543464097543166813054301 12578799036578687554895363)
                ·
                  refine ⟨18868198554868031332343045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12578799036578687554895363 18868198554868031332343045)
                  ·
                    refine ⟨3537787229037755874814321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18868198554868031332343045 3537787229037755874814321)
                    ·
                      refine ⟨2653340421778316906110741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537787229037755874814321 2653340421778316906110741)
                      ·
                        rfl

theorem cell23_5167362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5167362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167362 prefixEnd_5167362 := by exact prefixLift 5167362
  have htrace : WordTrace (prefixWord ++ tailWord_5167362) baseStart_5167362 baseEnd_5167362 := by
    simpa [prefixWord, tailWord_5167362, baseEnd_5167362] using wordTrace_append hprefix tailTrace_5167362
  have hstable : (prefixWord ++ tailWord_5167362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167362).length < 2 ^ (prefixWord ++ tailWord_5167362).sum := by decide
  have hdescent : baseEnd_5167362 < baseStart_5167362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167368 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 7]
def baseStart_5167368 : Nat := 118140960795 + 5167368 * 2 ^ 59
def prefixEnd_5167368 : Nat := 4983230072969 + 3 ^ 40 * 5167368 * 2
def baseEnd_5167368 : Nat := 294815944740249320292857

theorem tailTrace_5167368 : CollatzResearch.WordTrace tailWord_5167368 prefixEnd_5167368 294815944740249320292857 := by
  unfold tailWord_5167368
  simp only [CollatzResearch.WordTrace]
  refine ⟨94234697171757863519403379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125646262895677151359204505 94234697171757863519403379)
  ·
    refine ⟨141352045757636795279105069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94234697171757863519403379 141352045757636795279105069)
    ·
      refine ⟨53007017159113798229664401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141352045757636795279105069 53007017159113798229664401)
      ·
        refine ⟨39755262869335348672248301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53007017159113798229664401 39755262869335348672248301)
        ·
          refine ⟨14908223576000755752093113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39755262869335348672248301 14908223576000755752093113)
          ·
            refine ⟨11181167682000566814069835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14908223576000755752093113 11181167682000566814069835)
            ·
              refine ⟨16771751523000850221104753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11181167682000566814069835 16771751523000850221104753)
              ·
                refine ⟨12578813642250637665828565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16771751523000850221104753 12578813642250637665828565)
                ·
                  refine ⟨294815944740249320292857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12578813642250637665828565 294815944740249320292857)
                  ·
                    rfl

theorem cell23_5167368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_5167368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167368 prefixEnd_5167368 := by exact prefixLift 5167368
  have htrace : WordTrace (prefixWord ++ tailWord_5167368) baseStart_5167368 baseEnd_5167368 := by
    simpa [prefixWord, tailWord_5167368, baseEnd_5167368] using wordTrace_append hprefix tailTrace_5167368
  have hstable : (prefixWord ++ tailWord_5167368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167368).length < 2 ^ (prefixWord ++ tailWord_5167368).sum := by decide
  have hdescent : baseEnd_5167368 < baseStart_5167368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167418 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_5167418 : Nat := 118140960795 + 5167418 * 2 ^ 59
def prefixEnd_5167418 : Nat := 4983230072969 + 3 ^ 40 * 5167418 * 2
def baseEnd_5167418 : Nat := 2653369176694968687010483

theorem tailTrace_5167418 : CollatzResearch.WordTrace tailWord_5167418 prefixEnd_5167418 2653369176694968687010483 := by
  unfold tailWord_5167418
  simp only [CollatzResearch.WordTrace]
  refine ⟨47117804498333646394531727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125647478662223057052084605 47117804498333646394531727)
  ·
    refine ⟨70676706747500469591797591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47117804498333646394531727 70676706747500469591797591)
    ·
      refine ⟨106015060121250704387696387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70676706747500469591797591 106015060121250704387696387)
      ·
        refine ⟨159022590181876056581544581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106015060121250704387696387 159022590181876056581544581)
        ·
          refine ⟨29816735659101760609039609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159022590181876056581544581 29816735659101760609039609)
          ·
            refine ⟨22362551744326320456779707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29816735659101760609039609 22362551744326320456779707)
            ·
              refine ⟨33543827616489480685169561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22362551744326320456779707 33543827616489480685169561)
              ·
                refine ⟨25157870712367110513877171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33543827616489480685169561 25157870712367110513877171)
                ·
                  refine ⟨37736806068550665770815757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25157870712367110513877171 37736806068550665770815757)
                  ·
                    refine ⟨14151302275706499664055909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37736806068550665770815757 14151302275706499664055909)
                    ·
                      refine ⟨2653369176694968687010483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14151302275706499664055909 2653369176694968687010483)
                      ·
                        rfl

theorem cell23_5167418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_5167418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167418 prefixEnd_5167418 := by exact prefixLift 5167418
  have htrace : WordTrace (prefixWord ++ tailWord_5167418) baseStart_5167418 baseEnd_5167418 := by
    simpa [prefixWord, tailWord_5167418, baseEnd_5167418] using wordTrace_append hprefix tailTrace_5167418
  have hstable : (prefixWord ++ tailWord_5167418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167418).length < 2 ^ (prefixWord ++ tailWord_5167418).sum := by decide
  have hdescent : baseEnd_5167418 < baseStart_5167418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167519 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5167519 : Nat := 118140960795 + 5167519 * 2 ^ 59
def prefixEnd_5167519 : Nat := 4983230072969 + 3 ^ 40 * 5167519 * 2
def baseEnd_5167519 : Nat := 2653421038241072791847519

theorem tailTrace_5167519 : CollatzResearch.WordTrace tailWord_5167519 prefixEnd_5167519 2653421038241072791847519 := by
  unfold tailWord_5167519
  simp only [CollatzResearch.WordTrace]
  refine ⟨188474901765968679827553611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125649934510645786551702407 188474901765968679827553611)
  ·
    refine ⟨282712352648953019741330417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188474901765968679827553611 282712352648953019741330417)
    ·
      refine ⟨212034264486714764805997813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282712352648953019741330417 212034264486714764805997813)
      ·
        refine ⟨19878212295629509200562295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212034264486714764805997813 19878212295629509200562295)
        ·
          refine ⟨29817318443444263800843443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19878212295629509200562295 29817318443444263800843443)
          ·
            refine ⟨44725977665166395701265165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29817318443444263800843443 44725977665166395701265165)
            ·
              refine ⟨16772241624437398387974437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44725977665166395701265165 16772241624437398387974437)
              ·
                refine ⟨3144795304582012197745207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16772241624437398387974437 3144795304582012197745207)
                ·
                  refine ⟨4717192956873018296617811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144795304582012197745207 4717192956873018296617811)
                  ·
                    refine ⟨7075789435309527444926717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4717192956873018296617811 7075789435309527444926717)
                    ·
                      refine ⟨2653421038241072791847519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075789435309527444926717 2653421038241072791847519)
                      ·
                        rfl

theorem cell23_5167519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5167519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167519 prefixEnd_5167519 := by exact prefixLift 5167519
  have htrace : WordTrace (prefixWord ++ tailWord_5167519) baseStart_5167519 baseEnd_5167519 := by
    simpa [prefixWord, tailWord_5167519, baseEnd_5167519] using wordTrace_append hprefix tailTrace_5167519
  have hstable : (prefixWord ++ tailWord_5167519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167519).length < 2 ^ (prefixWord ++ tailWord_5167519).sum := by decide
  have hdescent : baseEnd_5167519 < baseStart_5167519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167556 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5167556 : Nat := 118140960795 + 5167556 * 2 ^ 59
def prefixEnd_5167556 : Nat := 4983230072969 + 3 ^ 40 * 5167556 * 2
def baseEnd_5167556 : Nat := 884480012341763049028283

theorem tailTrace_5167556 : CollatzResearch.WordTrace tailWord_5167556 prefixEnd_5167556 884480012341763049028283 := by
  unfold tailWord_5167556
  simp only [CollatzResearch.WordTrace]
  refine ⟨94238125633417317573325261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125650834177889756764433681 94238125633417317573325261)
  ·
    refine ⟨35339297112531494089996973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94238125633417317573325261 35339297112531494089996973)
    ·
      refine ⟨13252236417199310283748865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35339297112531494089996973 13252236417199310283748865)
      ·
        refine ⟨9939177312899482712811649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13252236417199310283748865 9939177312899482712811649)
        ·
          refine ⟨7454382984674612034608737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9939177312899482712811649 7454382984674612034608737)
          ·
            refine ⟨5590787238505959025956553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454382984674612034608737 5590787238505959025956553)
            ·
              refine ⟨4193090428879469269467415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5590787238505959025956553 4193090428879469269467415)
              ·
                refine ⟨6289635643319203904201123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193090428879469269467415 6289635643319203904201123)
                ·
                  refine ⟨9434453464978805856301685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289635643319203904201123 9434453464978805856301685)
                  ·
                    refine ⟨884480012341763049028283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9434453464978805856301685 884480012341763049028283)
                    ·
                      rfl

theorem cell23_5167556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5167556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167556 prefixEnd_5167556 := by exact prefixLift 5167556
  have htrace : WordTrace (prefixWord ++ tailWord_5167556) baseStart_5167556 baseEnd_5167556 := by
    simpa [prefixWord, tailWord_5167556, baseEnd_5167556] using wordTrace_append hprefix tailTrace_5167556
  have hstable : (prefixWord ++ tailWord_5167556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167556).length < 2 ^ (prefixWord ++ tailWord_5167556).sum := by decide
  have hdescent : baseEnd_5167556 < baseStart_5167556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167559 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_5167559 : Nat := 118140960795 + 5167559 * 2 ^ 59
def prefixEnd_5167559 : Nat := 4983230072969 + 3 ^ 40 * 5167559 * 2
def baseEnd_5167559 : Nat := 2653441577467252635347335

theorem tailTrace_5167559 : CollatzResearch.WordTrace tailWord_5167559 prefixEnd_5167559 2653441577467252635347335 := by
  unfold tailWord_5167559
  simp only [CollatzResearch.WordTrace]
  refine ⟨188476360685823766659009731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125650907123882511106006487 188476360685823766659009731)
  ·
    refine ⟨282714541028735649988514597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188476360685823766659009731 282714541028735649988514597)
    ·
      refine ⟨53008976442887934372846487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282714541028735649988514597 53008976442887934372846487)
      ·
        refine ⟨79513464664331901559269731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53008976442887934372846487 79513464664331901559269731)
        ·
          refine ⟨119270196996497852338904597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79513464664331901559269731 119270196996497852338904597)
          ·
            refine ⟨5590790484210836828386153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119270196996497852338904597 5590790484210836828386153)
            ·
              refine ⟨4193092863158127621289615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5590790484210836828386153 4193092863158127621289615)
              ·
                refine ⟨6289639294737191431934423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193092863158127621289615 6289639294737191431934423)
                ·
                  refine ⟨9434458942105787147901635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289639294737191431934423 9434458942105787147901635)
                  ·
                    refine ⟨14151688413158680721852453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9434458942105787147901635 14151688413158680721852453)
                    ·
                      refine ⟨2653441577467252635347335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14151688413158680721852453 2653441577467252635347335)
                      ·
                        rfl

theorem cell23_5167559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_5167559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167559 prefixEnd_5167559 := by exact prefixLift 5167559
  have htrace : WordTrace (prefixWord ++ tailWord_5167559) baseStart_5167559 baseEnd_5167559 := by
    simpa [prefixWord, tailWord_5167559, baseEnd_5167559] using wordTrace_append hprefix tailTrace_5167559
  have hstable : (prefixWord ++ tailWord_5167559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167559).length < 2 ^ (prefixWord ++ tailWord_5167559).sum := by decide
  have hdescent : baseEnd_5167559 < baseStart_5167559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167562 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_5167562 : Nat := 118140960795 + 5167562 * 2 ^ 59
def prefixEnd_5167562 : Nat := 4983230072969 + 3 ^ 40 * 5167562 * 2
def baseEnd_5167562 : Nat := 2653443117909216123609821

theorem tailTrace_5167562 : CollatzResearch.WordTrace tailWord_5167562 prefixEnd_5167562 2653443117909216123609821 := by
  unfold tailWord_5167562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47119117526203224542842235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125650980069875265447579293 47119117526203224542842235)
  ·
    refine ⟨70678676289304836814263353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47119117526203224542842235 70678676289304836814263353)
    ·
      refine ⟨53009007216978627610697515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70678676289304836814263353 53009007216978627610697515)
      ·
        refine ⟨79513510825467941416046273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53009007216978627610697515 79513510825467941416046273)
        ·
          refine ⟨59635133119100956062034705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79513510825467941416046273 59635133119100956062034705)
          ·
            refine ⟨44726349839325717046526029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59635133119100956062034705 44726349839325717046526029)
            ·
              refine ⟨16772381189747143892447261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44726349839325717046526029 16772381189747143892447261)
              ·
                refine ⟨6289642946155178959667723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16772381189747143892447261 6289642946155178959667723)
                ·
                  refine ⟨9434464419232768439501585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289642946155178959667723 9434464419232768439501585)
                  ·
                    refine ⟨7075848314424576329626189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9434464419232768439501585 7075848314424576329626189)
                    ·
                      refine ⟨2653443117909216123609821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075848314424576329626189 2653443117909216123609821)
                      ·
                        rfl

theorem cell23_5167562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_5167562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167562 prefixEnd_5167562 := by exact prefixLift 5167562
  have htrace : WordTrace (prefixWord ++ tailWord_5167562) baseStart_5167562 baseEnd_5167562 := by
    simpa [prefixWord, tailWord_5167562, baseEnd_5167562] using wordTrace_append hprefix tailTrace_5167562
  have hstable : (prefixWord ++ tailWord_5167562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167562).length < 2 ^ (prefixWord ++ tailWord_5167562).sum := by decide
  have hdescent : baseEnd_5167562 < baseStart_5167562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167586 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5167586 : Nat := 118140960795 + 5167586 * 2 ^ 59
def prefixEnd_5167586 : Nat := 4983230072969 + 3 ^ 40 * 5167586 * 2
def baseEnd_5167586 : Nat := 884485147148308009903237

theorem tailTrace_5167586 : CollatzResearch.WordTrace tailWord_5167586 prefixEnd_5167586 884485147148308009903237 := by
  unfold tailWord_5167586
  simp only [CollatzResearch.WordTrace]
  refine ⟨47119336364181487567560653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125651563637817300180161741 47119336364181487567560653)
  ·
    refine ⟨17669751136568057837835245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47119336364181487567560653 17669751136568057837835245)
    ·
      refine ⟨6626156676213021689188217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17669751136568057837835245 6626156676213021689188217)
      ·
        refine ⟨4969617507159766266891163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6626156676213021689188217 4969617507159766266891163)
        ·
          refine ⟨7454426260739649400336745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969617507159766266891163 7454426260739649400336745)
          ·
            refine ⟨5590819695554737050252559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454426260739649400336745 5590819695554737050252559)
            ·
              refine ⟨8386229543332105575378839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590819695554737050252559 8386229543332105575378839)
              ·
                refine ⟨12579344314998158363068259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386229543332105575378839 12579344314998158363068259)
                ·
                  refine ⟨18869016472497237544602389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12579344314998158363068259 18869016472497237544602389)
                  ·
                    refine ⟨884485147148308009903237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18869016472497237544602389 884485147148308009903237)
                    ·
                      rfl

theorem cell23_5167586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5167586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167586 prefixEnd_5167586 := by exact prefixLift 5167586
  have htrace : WordTrace (prefixWord ++ tailWord_5167586) baseStart_5167586 baseEnd_5167586 := by
    simpa [prefixWord, tailWord_5167586, baseEnd_5167586] using wordTrace_append hprefix tailTrace_5167586
  have hstable : (prefixWord ++ tailWord_5167586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167586).length < 2 ^ (prefixWord ++ tailWord_5167586).sum := by decide
  have hdescent : baseEnd_5167586 < baseStart_5167586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167589 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_5167589 : Nat := 118140960795 + 5167589 * 2 ^ 59
def prefixEnd_5167589 : Nat := 4983230072969 + 3 ^ 40 * 5167589 * 2
def baseEnd_5167589 : Nat := 2653456981886887517972197

theorem tailTrace_5167589 : CollatzResearch.WordTrace tailWord_5167589 prefixEnd_5167589 2653456981886887517972197 := by
  unfold tailWord_5167589
  simp only [CollatzResearch.WordTrace]
  refine ⟨188477454875715081782601821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125651636583810054521734547 188477454875715081782601821)
  ·
    refine ⟨70679045578393155668475683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188477454875715081782601821 70679045578393155668475683)
    ·
      refine ⟨106018568367589733502713525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70679045578393155668475683 106018568367589733502713525)
      ·
        refine ⟨9939240784461537515879393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106018568367589733502713525 9939240784461537515879393)
        ·
          refine ⟨7454430588346153136909545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9939240784461537515879393 7454430588346153136909545)
          ·
            refine ⟨5590822941259614852682159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454430588346153136909545 5590822941259614852682159)
            ·
              refine ⟨8386234411889422279023239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590822941259614852682159 8386234411889422279023239)
              ·
                refine ⟨12579351617834133418534859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386234411889422279023239 12579351617834133418534859)
                ·
                  refine ⟨18869027426751200127802289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12579351617834133418534859 18869027426751200127802289)
                  ·
                    refine ⟨14151770570063400095851717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18869027426751200127802289 14151770570063400095851717)
                    ·
                      refine ⟨2653456981886887517972197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14151770570063400095851717 2653456981886887517972197)
                      ·
                        rfl

theorem cell23_5167589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_5167589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167589 prefixEnd_5167589 := by exact prefixLift 5167589
  have htrace : WordTrace (prefixWord ++ tailWord_5167589) baseStart_5167589 baseEnd_5167589 := by
    simpa [prefixWord, tailWord_5167589, baseEnd_5167589] using wordTrace_append hprefix tailTrace_5167589
  have hstable : (prefixWord ++ tailWord_5167589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167589).length < 2 ^ (prefixWord ++ tailWord_5167589).sum := by decide
  have hdescent : baseEnd_5167589 < baseStart_5167589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167592 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5167592 : Nat := 118140960795 + 5167592 * 2 ^ 59
def prefixEnd_5167592 : Nat := 4983230072969 + 3 ^ 40 * 5167592 * 2
def baseEnd_5167592 : Nat := 2653458522328851006234683

theorem tailTrace_5167592 : CollatzResearch.WordTrace tailWord_5167592 prefixEnd_5167592 2653458522328851006234683 := by
  unfold tailWord_5167592
  simp only [CollatzResearch.WordTrace]
  refine ⟨94238782147352106647480515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125651709529802808863307353 94238782147352106647480515)
  ·
    refine ⟨141358173221028159971220773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94238782147352106647480515 141358173221028159971220773)
    ·
      refine ⟨26504657478942779994603895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141358173221028159971220773 26504657478942779994603895)
      ·
        refine ⟨39756986218414169991905843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26504657478942779994603895 39756986218414169991905843)
        ·
          refine ⟨59635479327621254987858765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39756986218414169991905843 59635479327621254987858765)
          ·
            refine ⟨22363304747857970620447037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59635479327621254987858765 22363304747857970620447037)
            ·
              refine ⟨8386239280446738982667639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22363304747857970620447037 8386239280446738982667639)
              ·
                refine ⟨12579358920670108474001459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386239280446738982667639 12579358920670108474001459)
                ·
                  refine ⟨18869038381005162711002189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12579358920670108474001459 18869038381005162711002189)
                  ·
                    refine ⟨7075889392876936016625821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18869038381005162711002189 7075889392876936016625821)
                    ·
                      refine ⟨2653458522328851006234683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075889392876936016625821 2653458522328851006234683)
                      ·
                        rfl

theorem cell23_5167592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5167592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167592 prefixEnd_5167592 := by exact prefixLift 5167592
  have htrace : WordTrace (prefixWord ++ tailWord_5167592) baseStart_5167592 baseEnd_5167592 := by
    simpa [prefixWord, tailWord_5167592, baseEnd_5167592] using wordTrace_append hprefix tailTrace_5167592
  have hstable : (prefixWord ++ tailWord_5167592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167592).length < 2 ^ (prefixWord ++ tailWord_5167592).sum := by decide
  have hdescent : baseEnd_5167592 < baseStart_5167592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167635 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3]
def baseStart_5167635 : Nat := 118140960795 + 5167635 * 2 ^ 59
def prefixEnd_5167635 : Nat := 4983230072969 + 3 ^ 40 * 5167635 * 2
def baseEnd_5167635 : Nat := 2653480601996994337996985

theorem tailTrace_5167635 : CollatzResearch.WordTrace tailWord_5167635 prefixEnd_5167635 2653480601996994337996985 := by
  unfold tailWord_5167635
  simp only [CollatzResearch.WordTrace]
  refine ⟨188479132633548431638776359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125652755089032287759184239 188479132633548431638776359)
  ·
    refine ⟨282718698950322647458164539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188479132633548431638776359 282718698950322647458164539)
    ·
      refine ⟨424078048425483971187246809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282718698950322647458164539 424078048425483971187246809)
      ·
        refine ⟨318058536319112978390435107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424078048425483971187246809 318058536319112978390435107)
        ·
          refine ⟨477087804478669467585652661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318058536319112978390435107 477087804478669467585652661)
          ·
            refine ⟨44726981669875262586154937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 477087804478669467585652661 44726981669875262586154937)
            ·
              refine ⟨33545236252406446939616203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44726981669875262586154937 33545236252406446939616203)
              ·
                refine ⟨50317854378609670409424305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33545236252406446939616203 50317854378609670409424305)
                ·
                  refine ⟨37738390783957252807068229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50317854378609670409424305 37738390783957252807068229)
                  ·
                    refine ⟨7075948271991984901325293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37738390783957252807068229 7075948271991984901325293)
                    ·
                      refine ⟨2653480601996994337996985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7075948271991984901325293 2653480601996994337996985)
                      ·
                        rfl

theorem cell23_5167635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_5167635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167635 prefixEnd_5167635 := by exact prefixLift 5167635
  have htrace : WordTrace (prefixWord ++ tailWord_5167635) baseStart_5167635 baseEnd_5167635 := by
    simpa [prefixWord, tailWord_5167635, baseEnd_5167635] using wordTrace_append hprefix tailTrace_5167635
  have hstable : (prefixWord ++ tailWord_5167635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167635).length < 2 ^ (prefixWord ++ tailWord_5167635).sum := by decide
  have hdescent : baseEnd_5167635 < baseStart_5167635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167672 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 5]
def baseStart_5167672 : Nat := 118140960795 + 5167672 * 2 ^ 59
def prefixEnd_5167672 : Nat := 4983230072969 + 3 ^ 40 * 5167672 * 2
def baseEnd_5167672 : Nat := 294833288975690077026035

theorem tailTrace_5167672 : CollatzResearch.WordTrace tailWord_5167672 prefixEnd_5167672 294833288975690077026035 := by
  unfold tailWord_5167672
  simp only [CollatzResearch.WordTrace]
  refine ⟨94240241067207193478936635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125653654756276257971915513 94240241067207193478936635)
  ·
    refine ⟨141360361600810790218404953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94240241067207193478936635 141360361600810790218404953)
    ·
      refine ⟨106020271200608092663803715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141360361600810790218404953 106020271200608092663803715)
      ·
        refine ⟨159030406800912138995705573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106020271200608092663803715 159030406800912138995705573)
        ·
          refine ⟨29818201275171026061694795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159030406800912138995705573 29818201275171026061694795)
          ·
            refine ⟨44727301912756539092542193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29818201275171026061694795 44727301912756539092542193)
            ·
              refine ⟨33545476434567404319406645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44727301912756539092542193 33545476434567404319406645)
              ·
                refine ⟨3144888415740694154944373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33545476434567404319406645 3144888415740694154944373)
                ·
                  refine ⟨294833288975690077026035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3144888415740694154944373 294833288975690077026035)
                  ·
                    rfl

theorem cell23_5167672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 5].length) (baseStart_5167672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167672 prefixEnd_5167672 := by exact prefixLift 5167672
  have htrace : WordTrace (prefixWord ++ tailWord_5167672) baseStart_5167672 baseEnd_5167672 := by
    simpa [prefixWord, tailWord_5167672, baseEnd_5167672] using wordTrace_append hprefix tailTrace_5167672
  have hstable : (prefixWord ++ tailWord_5167672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167672).length < 2 ^ (prefixWord ++ tailWord_5167672).sum := by decide
  have hdescent : baseEnd_5167672 < baseStart_5167672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167692 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5167692 : Nat := 118140960795 + 5167692 * 2 ^ 59
def prefixEnd_5167692 : Nat := 4983230072969 + 3 ^ 40 * 5167692 * 2
def baseEnd_5167692 : Nat := 2653509870394300614984223

theorem tailTrace_5167692 : CollatzResearch.WordTrace tailWord_5167692 prefixEnd_5167692 2653509870394300614984223 := by
  unfold tailWord_5167692
  simp only [CollatzResearch.WordTrace]
  refine ⟨94240605797170965186800665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125654141062894620249067553 94240605797170965186800665)
  ·
    refine ⟨70680454347878223890100499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94240605797170965186800665 70680454347878223890100499)
    ·
      refine ⟨106020681521817335835150749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70680454347878223890100499 106020681521817335835150749)
      ·
        refine ⟨39757755570681500938181531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106020681521817335835150749 39757755570681500938181531)
        ·
          refine ⟨59636633356022251407272297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39757755570681500938181531 59636633356022251407272297)
          ·
            refine ⟨44727475017016688555454223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59636633356022251407272297 44727475017016688555454223)
            ·
              refine ⟨67091212525525032833181335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44727475017016688555454223 67091212525525032833181335)
              ·
                refine ⟨100636818788287549249772003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67091212525525032833181335 100636818788287549249772003)
                ·
                  refine ⟨150955228182431323874658005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100636818788287549249772003 150955228182431323874658005)
                  ·
                    refine ⟨3538013160525734153312297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 150955228182431323874658005 3538013160525734153312297)
                    ·
                      refine ⟨2653509870394300614984223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538013160525734153312297 2653509870394300614984223)
                      ·
                        rfl

theorem cell23_5167692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5167692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167692 prefixEnd_5167692 := by exact prefixLift 5167692
  have htrace : WordTrace (prefixWord ++ tailWord_5167692) baseStart_5167692 baseEnd_5167692 := by
    simpa [prefixWord, tailWord_5167692, baseEnd_5167692] using wordTrace_append hprefix tailTrace_5167692
  have hstable : (prefixWord ++ tailWord_5167692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167692).length < 2 ^ (prefixWord ++ tailWord_5167692).sum := by decide
  have hdescent : baseEnd_5167692 < baseStart_5167692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167695 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_5167695 : Nat := 118140960795 + 5167695 * 2 ^ 59
def prefixEnd_5167695 : Nat := 4983230072969 + 3 ^ 40 * 5167695 * 2
def baseEnd_5167695 : Nat := 2653511410836264103246709

theorem tailTrace_5167695 : CollatzResearch.WordTrace tailWord_5167695 prefixEnd_5167695 2653511410836264103246709 := by
  unfold tailWord_5167695
  simp only [CollatzResearch.WordTrace]
  refine ⟨188481321013331061885960539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125654214008887374590640359 188481321013331061885960539)
  ·
    refine ⟨282721981519996592828940809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188481321013331061885960539 282721981519996592828940809)
    ·
      refine ⟨212041486139997444621705607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282721981519996592828940809 212041486139997444621705607)
      ·
        refine ⟨318062229209996166932558411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212041486139997444621705607 318062229209996166932558411)
        ·
          refine ⟨477093343814994250398837617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318062229209996166932558411 477093343814994250398837617)
          ·
            refine ⟨357820007861245687799128213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477093343814994250398837617 357820007861245687799128213)
            ·
              refine ⟨16772812868495891615584135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 357820007861245687799128213 16772812868495891615584135)
              ·
                refine ⟨25159219302743837423376203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16772812868495891615584135 25159219302743837423376203)
                ·
                  refine ⟨37738828954115756135064305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25159219302743837423376203 37738828954115756135064305)
                  ·
                    refine ⟨28304121715586817101298229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37738828954115756135064305 28304121715586817101298229)
                    ·
                      refine ⟨2653511410836264103246709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28304121715586817101298229 2653511410836264103246709)
                      ·
                        rfl

theorem cell23_5167695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_5167695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167695 prefixEnd_5167695 := by exact prefixLift 5167695
  have htrace : WordTrace (prefixWord ++ tailWord_5167695) baseStart_5167695 baseEnd_5167695 := by
    simpa [prefixWord, tailWord_5167695, baseEnd_5167695] using wordTrace_append hprefix tailTrace_5167695
  have hstable : (prefixWord ++ tailWord_5167695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167695).length < 2 ^ (prefixWord ++ tailWord_5167695).sum := by decide
  have hdescent : baseEnd_5167695 < baseStart_5167695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167722 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5167722 : Nat := 118140960795 + 5167722 * 2 ^ 59
def prefixEnd_5167722 : Nat := 4983230072969 + 3 ^ 40 * 5167722 * 2
def baseEnd_5167722 : Nat := 2653525274813935497609085

theorem tailTrace_5167722 : CollatzResearch.WordTrace tailWord_5167722 prefixEnd_5167722 2653525274813935497609085 := by
  unfold tailWord_5167722
  simp only [CollatzResearch.WordTrace]
  refine ⟨47120576446058311374298355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125654870522822163664795613 47120576446058311374298355)
  ·
    refine ⟨70680864669087467061447533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47120576446058311374298355 70680864669087467061447533)
    ·
      refine ⟨26505324250907800148042825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70680864669087467061447533 26505324250907800148042825)
      ·
        refine ⟨19878993188180850111032119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26505324250907800148042825 19878993188180850111032119)
        ·
          refine ⟨29818489782271275166548179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19878993188180850111032119 29818489782271275166548179)
          ·
            refine ⟨44727734673406912749822269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29818489782271275166548179 44727734673406912749822269)
            ·
              refine ⟨16772900502527592281183351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44727734673406912749822269 16772900502527592281183351)
              ·
                refine ⟨25159350753791388421775027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16772900502527592281183351 25159350753791388421775027)
                ·
                  refine ⟨37739026130687082632662541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25159350753791388421775027 37739026130687082632662541)
                  ·
                    refine ⟨14152134799007655987248453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37739026130687082632662541 14152134799007655987248453)
                    ·
                      refine ⟨2653525274813935497609085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14152134799007655987248453 2653525274813935497609085)
                      ·
                        rfl

theorem cell23_5167722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5167722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167722 prefixEnd_5167722 := by exact prefixLift 5167722
  have htrace : WordTrace (prefixWord ++ tailWord_5167722) baseStart_5167722 baseEnd_5167722 := by
    simpa [prefixWord, tailWord_5167722, baseEnd_5167722] using wordTrace_append hprefix tailTrace_5167722
  have hstable : (prefixWord ++ tailWord_5167722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167722).length < 2 ^ (prefixWord ++ tailWord_5167722).sum := by decide
  have hdescent : baseEnd_5167722 < baseStart_5167722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167735 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_5167735 : Nat := 118140960795 + 5167735 * 2 ^ 59
def prefixEnd_5167735 : Nat := 4983230072969 + 3 ^ 40 * 5167735 * 2
def baseEnd_5167735 : Nat := 2653531950062443946746525

theorem tailTrace_5167735 : CollatzResearch.WordTrace tailWord_5167735 prefixEnd_5167735 2653531950062443946746525 := by
  unfold tailWord_5167735
  simp only [CollatzResearch.WordTrace]
  refine ⟨188482779933186148717416659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125655186622124099144944439 188482779933186148717416659)
  ·
    refine ⟨282724169899779223076124989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188482779933186148717416659 282724169899779223076124989)
    ·
      refine ⟨106021563712417208653546871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282724169899779223076124989 106021563712417208653546871)
      ·
        refine ⟨159032345568625812980320307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106021563712417208653546871 159032345568625812980320307)
        ·
          refine ⟨238548518352938719470480461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159032345568625812980320307 238548518352938719470480461)
          ·
            refine ⟨89455694382352019801430173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238548518352938719470480461 89455694382352019801430173)
            ·
              refine ⟨33545885393382007425536315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89455694382352019801430173 33545885393382007425536315)
              ·
                refine ⟨50318828090073011138304473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33545885393382007425536315 50318828090073011138304473)
                ·
                  refine ⟨37739121067554758353728355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50318828090073011138304473 37739121067554758353728355)
                  ·
                    refine ⟨56608681601332137530592533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37739121067554758353728355 56608681601332137530592533)
                    ·
                      refine ⟨2653531950062443946746525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56608681601332137530592533 2653531950062443946746525)
                      ·
                        rfl

theorem cell23_5167735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_5167735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167735 prefixEnd_5167735 := by exact prefixLift 5167735
  have htrace : WordTrace (prefixWord ++ tailWord_5167735) baseStart_5167735 baseEnd_5167735 := by
    simpa [prefixWord, tailWord_5167735, baseEnd_5167735] using wordTrace_append hprefix tailTrace_5167735
  have hstable : (prefixWord ++ tailWord_5167735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167735).length < 2 ^ (prefixWord ++ tailWord_5167735).sum := by decide
  have hdescent : baseEnd_5167735 < baseStart_5167735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167749 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_5167749 : Nat := 118140960795 + 5167749 * 2 ^ 59
def prefixEnd_5167749 : Nat := 4983230072969 + 3 ^ 40 * 5167749 * 2
def baseEnd_5167749 : Nat := 884513046263868963990487

theorem tailTrace_5167749 : CollatzResearch.WordTrace tailWord_5167749 prefixEnd_5167749 884513046263868963990487 := by
  unfold tailWord_5167749
  simp only [CollatzResearch.WordTrace]
  refine ⟨188483290555135429108426301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125655527036756952738950867 188483290555135429108426301)
  ·
    refine ⟨70681233958175785915659863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188483290555135429108426301 70681233958175785915659863)
    ·
      refine ⟨106021850937263678873489795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70681233958175785915659863 106021850937263678873489795)
      ·
        refine ⟨159032776405895518310234693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106021850937263678873489795 159032776405895518310234693)
        ·
          refine ⟨29818645576105409683169005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159032776405895518310234693 29818645576105409683169005)
          ·
            refine ⟨11181992091039528631188377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29818645576105409683169005 11181992091039528631188377)
            ·
              refine ⟨8386494068279646473391283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11181992091039528631188377 8386494068279646473391283)
              ·
                refine ⟨12579741102419469710086925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386494068279646473391283 12579741102419469710086925)
                ·
                  refine ⟨4717402913407301141282597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12579741102419469710086925 4717402913407301141282597)
                  ·
                    refine ⟨884513046263868963990487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4717402913407301141282597 884513046263868963990487)
                    ·
                      rfl

theorem cell23_5167749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_5167749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167749 prefixEnd_5167749 := by exact prefixLift 5167749
  have htrace : WordTrace (prefixWord ++ tailWord_5167749) baseStart_5167749 baseEnd_5167749 := by
    simpa [prefixWord, tailWord_5167749, baseEnd_5167749] using wordTrace_append hprefix tailTrace_5167749
  have hstable : (prefixWord ++ tailWord_5167749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167749).length < 2 ^ (prefixWord ++ tailWord_5167749).sum := by decide
  have hdescent : baseEnd_5167749 < baseStart_5167749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167785 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_5167785 : Nat := 118140960795 + 5167785 * 2 ^ 59
def prefixEnd_5167785 : Nat := 4983230072969 + 3 ^ 40 * 5167785 * 2
def baseEnd_5167785 : Nat := 2653557624095168751121295

theorem tailTrace_5167785 : CollatzResearch.WordTrace tailWord_5167785 prefixEnd_5167785 2653557624095168751121295 := by
  unfold tailWord_5167785
  simp only [CollatzResearch.WordTrace]
  refine ⟨188484603583005007256736809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125656402388670004837824539 188484603583005007256736809)
  ·
    refine ⟨141363452687253755442552607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188484603583005007256736809 141363452687253755442552607)
    ·
      refine ⟨212045179030880633163828911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141363452687253755442552607 212045179030880633163828911)
      ·
        refine ⟨318067768546320949745743367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212045179030880633163828911 318067768546320949745743367)
        ·
          refine ⟨477101652819481424618615051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318067768546320949745743367 477101652819481424618615051)
          ·
            refine ⟨715652479229222136927922577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477101652819481424618615051 715652479229222136927922577)
            ·
              refine ⟨536739359421916602695941933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715652479229222136927922577 536739359421916602695941933)
              ·
                refine ⟨201277259783218726010978225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536739359421916602695941933 201277259783218726010978225)
                ·
                  refine ⟨150957944837414044508233669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201277259783218726010978225 150957944837414044508233669)
                  ·
                    refine ⟨28304614657015133345293813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150957944837414044508233669 28304614657015133345293813)
                    ·
                      refine ⟨2653557624095168751121295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28304614657015133345293813 2653557624095168751121295)
                      ·
                        rfl

theorem cell23_5167785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_5167785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167785 prefixEnd_5167785 := by exact prefixLift 5167785
  have htrace : WordTrace (prefixWord ++ tailWord_5167785) baseStart_5167785 baseEnd_5167785 := by
    simpa [prefixWord, tailWord_5167785, baseEnd_5167785] using wordTrace_append hprefix tailTrace_5167785
  have hstable : (prefixWord ++ tailWord_5167785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167785).length < 2 ^ (prefixWord ++ tailWord_5167785).sum := by decide
  have hdescent : baseEnd_5167785 < baseStart_5167785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167849 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_5167849 : Nat := 118140960795 + 5167849 * 2 ^ 59
def prefixEnd_5167849 : Nat := 4983230072969 + 3 ^ 40 * 5167849 * 2
def baseEnd_5167849 : Nat := 2653590486857056500721001

theorem tailTrace_5167849 : CollatzResearch.WordTrace tailWord_5167849 prefixEnd_5167849 2653590486857056500721001 := by
  unfold tailWord_5167849
  simp only [CollatzResearch.WordTrace]
  refine ⟨188486937854773146187066601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125657958569848764124711067 188486937854773146187066601)
  ·
    refine ⟨141365203391079859640299951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188486937854773146187066601 141365203391079859640299951)
    ·
      refine ⟨212047805086619789460449927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141365203391079859640299951 212047805086619789460449927)
      ·
        refine ⟨318071707629929684190674891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212047805086619789460449927 318071707629929684190674891)
        ·
          refine ⟨477107561444894526286012337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318071707629929684190674891 477107561444894526286012337)
          ·
            refine ⟨357830671083670894714509253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477107561444894526286012337 357830671083670894714509253)
            ·
              refine ⟨67093250828188292758970485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357830671083670894714509253 67093250828188292758970485)
              ·
                refine ⟨6289992265142652446153483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67093250828188292758970485 6289992265142652446153483)
                ·
                  refine ⟨9434988397713978669230225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6289992265142652446153483 9434988397713978669230225)
                  ·
                    refine ⟨7076241298285484001922669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9434988397713978669230225 7076241298285484001922669)
                    ·
                      refine ⟨2653590486857056500721001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7076241298285484001922669 2653590486857056500721001)
                      ·
                        rfl

theorem cell23_5167849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_5167849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167849 prefixEnd_5167849 := by exact prefixLift 5167849
  have htrace : WordTrace (prefixWord ++ tailWord_5167849) baseStart_5167849 baseEnd_5167849 := by
    simpa [prefixWord, tailWord_5167849, baseEnd_5167849] using wordTrace_append hprefix tailTrace_5167849
  have hstable : (prefixWord ++ tailWord_5167849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167849).length < 2 ^ (prefixWord ++ tailWord_5167849).sum := by decide
  have hdescent : baseEnd_5167849 < baseStart_5167849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167882 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_5167882 : Nat := 118140960795 + 5167882 * 2 ^ 59
def prefixEnd_5167882 : Nat := 4983230072969 + 3 ^ 40 * 5167882 * 2
def baseEnd_5167882 : Nat := 884535810572884957202783

theorem tailTrace_5167882 : CollatzResearch.WordTrace tailWord_5167882 prefixEnd_5167882 884535810572884957202783 := by
  unfold tailWord_5167882
  simp only [CollatzResearch.WordTrace]
  refine ⟨47122035365913398205754475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125658760975769061882011933 47122035365913398205754475)
  ·
    refine ⟨70683053048870097308631713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47122035365913398205754475 70683053048870097308631713)
    ·
      refine ⟨53012289786652572981473785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70683053048870097308631713 53012289786652572981473785)
      ·
        refine ⟨39759217339989429736105339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53012289786652572981473785 39759217339989429736105339)
        ·
          refine ⟨59638826009984144604158009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39759217339989429736105339 59638826009984144604158009)
          ·
            refine ⟨44729119507488108453118507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59638826009984144604158009 44729119507488108453118507)
            ·
              refine ⟨67093679261232162679677761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44729119507488108453118507 67093679261232162679677761)
              ·
                refine ⟨50320259445924122009758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67093679261232162679677761 50320259445924122009758321)
                ·
                  refine ⟨37740194584443091507318741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50320259445924122009758321 37740194584443091507318741)
                  ·
                    refine ⟨884535810572884957202783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37740194584443091507318741 884535810572884957202783)
                    ·
                      rfl

theorem cell23_5167882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_5167882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167882 prefixEnd_5167882 := by exact prefixLift 5167882
  have htrace : WordTrace (prefixWord ++ tailWord_5167882) baseStart_5167882 baseEnd_5167882 := by
    simpa [prefixWord, tailWord_5167882, baseEnd_5167882] using wordTrace_append hprefix tailTrace_5167882
  have hstable : (prefixWord ++ tailWord_5167882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167882).length < 2 ^ (prefixWord ++ tailWord_5167882).sum := by decide
  have hdescent : baseEnd_5167882 < baseStart_5167882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167930 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_5167930 : Nat := 118140960795 + 5167930 * 2 ^ 59
def prefixEnd_5167930 : Nat := 4983230072969 + 3 ^ 40 * 5167930 * 2
def baseEnd_5167930 : Nat := 2653632078790070683808129

theorem tailTrace_5167930 : CollatzResearch.WordTrace tailWord_5167930 prefixEnd_5167930 2653632078790070683808129 := by
  unfold tailWord_5167930
  simp only [CollatzResearch.WordTrace]
  refine ⟨47122473041869924255191311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125659928111653131347176829 47122473041869924255191311)
  ·
    refine ⟨70683709562804886382786967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47122473041869924255191311 70683709562804886382786967)
    ·
      refine ⟨106025564344207329574180451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70683709562804886382786967 106025564344207329574180451)
      ·
        refine ⟨159038346516310994361270677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106025564344207329574180451 159038346516310994361270677)
        ·
          refine ⟨7454922492952077860684563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159038346516310994361270677 7454922492952077860684563)
          ·
            refine ⟨11182383739428116791026845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7454922492952077860684563 11182383739428116791026845)
            ·
              refine ⟨4193393902285543796635067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11182383739428116791026845 4193393902285543796635067)
              ·
                refine ⟨6290090853428315694952601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193393902285543796635067 6290090853428315694952601)
                ·
                  refine ⟨4717568140071236771214451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290090853428315694952601 4717568140071236771214451)
                  ·
                    refine ⟨7076352210106855156821677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4717568140071236771214451 7076352210106855156821677)
                    ·
                      refine ⟨2653632078790070683808129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7076352210106855156821677 2653632078790070683808129)
                      ·
                        rfl

theorem cell23_5167930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_5167930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167930 prefixEnd_5167930 := by exact prefixLift 5167930
  have htrace : WordTrace (prefixWord ++ tailWord_5167930) baseStart_5167930 baseEnd_5167930 := by
    simpa [prefixWord, tailWord_5167930, baseEnd_5167930] using wordTrace_append hprefix tailTrace_5167930
  have hstable : (prefixWord ++ tailWord_5167930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167930).length < 2 ^ (prefixWord ++ tailWord_5167930).sum := by decide
  have hdescent : baseEnd_5167930 < baseStart_5167930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167956 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_5167956 : Nat := 118140960795 + 5167956 * 2 ^ 59
def prefixEnd_5167956 : Nat := 4983230072969 + 3 ^ 40 * 5167956 * 2
def baseEnd_5167956 : Nat := 2653645429287087582083009

theorem tailTrace_5167956 : CollatzResearch.WordTrace tailWord_5167956 prefixEnd_5167956 2653645429287087582083009 := by
  unfold tailWord_5167956
  simp only [CollatzResearch.WordTrace]
  refine ⟨94245420232692751730605861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125660560310257002307474481 94245420232692751730605861)
  ·
    refine ⟨17671016293629890949488599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94245420232692751730605861 17671016293629890949488599)
    ·
      refine ⟨26506524440444836424232899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671016293629890949488599 26506524440444836424232899)
      ·
        refine ⟨39759786660667254636349349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26506524440444836424232899 39759786660667254636349349)
        ·
          refine ⟨7454959998875110244315503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39759786660667254636349349 7454959998875110244315503)
          ·
            refine ⟨11182439998312665366473255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7454959998875110244315503 11182439998312665366473255)
            ·
              refine ⟨16773659997468998049709883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182439998312665366473255 16773659997468998049709883)
              ·
                refine ⟨25160489996203497074564825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16773659997468998049709883 25160489996203497074564825)
                ·
                  refine ⟨18870367497152622805923619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25160489996203497074564825 18870367497152622805923619)
                  ·
                    refine ⟨28305551245728934208885429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18870367497152622805923619 28305551245728934208885429)
                    ·
                      refine ⟨2653645429287087582083009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28305551245728934208885429 2653645429287087582083009)
                      ·
                        rfl

theorem cell23_5167956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_5167956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167956 prefixEnd_5167956 := by exact prefixLift 5167956
  have htrace : WordTrace (prefixWord ++ tailWord_5167956) baseStart_5167956 baseEnd_5167956 := by
    simpa [prefixWord, tailWord_5167956, baseEnd_5167956] using wordTrace_append hprefix tailTrace_5167956
  have hstable : (prefixWord ++ tailWord_5167956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167956).length < 2 ^ (prefixWord ++ tailWord_5167956).sum := by decide
  have hdescent : baseEnd_5167956 < baseStart_5167956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167969 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_5167969 : Nat := 118140960795 + 5167969 * 2 ^ 59
def prefixEnd_5167969 : Nat := 4983230072969 + 3 ^ 40 * 5167969 * 2
def baseEnd_5167969 : Nat := 2653652104535596031220449

theorem tailTrace_5167969 : CollatzResearch.WordTrace tailWord_5167969 prefixEnd_5167969 2653652104535596031220449 := by
  unfold tailWord_5167969
  simp only [CollatzResearch.WordTrace]
  refine ⟨188491314614338406681434961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125660876409558937787623307 188491314614338406681434961)
  ·
    refine ⟨141368485960753805011076221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188491314614338406681434961 141368485960753805011076221)
    ·
      refine ⟨53013182235282676879153583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141368485960753805011076221 53013182235282676879153583)
      ·
        refine ⟨79519773352924015318730375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53013182235282676879153583 79519773352924015318730375)
        ·
          refine ⟨119279660029386022978095563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79519773352924015318730375 119279660029386022978095563)
          ·
            refine ⟨178919490044079034467143345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119279660029386022978095563 178919490044079034467143345)
            ·
              refine ⟨134189617533059275850357509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178919490044079034467143345 134189617533059275850357509)
              ·
                refine ⟨25160553287448614221942033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134189617533059275850357509 25160553287448614221942033)
                ·
                  refine ⟨18870414965586460666456525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25160553287448614221942033 18870414965586460666456525)
                  ·
                    refine ⟨7076405612094922749921197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18870414965586460666456525 7076405612094922749921197)
                    ·
                      refine ⟨2653652104535596031220449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7076405612094922749921197 2653652104535596031220449)
                      ·
                        rfl

theorem cell23_5167969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_5167969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167969 prefixEnd_5167969 := by exact prefixLift 5167969
  have htrace : WordTrace (prefixWord ++ tailWord_5167969) baseStart_5167969 baseEnd_5167969 := by
    simpa [prefixWord, tailWord_5167969, baseEnd_5167969] using wordTrace_append hprefix tailTrace_5167969
  have hstable : (prefixWord ++ tailWord_5167969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167969).length < 2 ^ (prefixWord ++ tailWord_5167969).sum := by decide
  have hdescent : baseEnd_5167969 < baseStart_5167969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5167976 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 7]
def baseStart_5167976 : Nat := 118140960795 + 5167976 * 2 ^ 59
def prefixEnd_5167976 : Nat := 4983230072969 + 3 ^ 40 * 5167976 * 2
def baseEnd_5167976 : Nat := 294850633211130833759213

theorem tailTrace_5167976 : CollatzResearch.WordTrace tailWord_5167976 prefixEnd_5167976 294850633211130833759213 := by
  unfold tailWord_5167976
  simp only [CollatzResearch.WordTrace]
  refine ⟨94245784962656523438469891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125661046616875364584626521 94245784962656523438469891)
  ·
    refine ⟨141368677443984785157704837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94245784962656523438469891 141368677443984785157704837)
    ·
      refine ⟨26506627020747147217069657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141368677443984785157704837 26506627020747147217069657)
      ·
        refine ⟨19879970265560360412802243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26506627020747147217069657 19879970265560360412802243)
        ·
          refine ⟨29819955398340540619203365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19879970265560360412802243 29819955398340540619203365)
          ·
            refine ⟨5591241637188851366100631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29819955398340540619203365 5591241637188851366100631)
            ·
              refine ⟨8386862455783277049150947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591241637188851366100631 8386862455783277049150947)
              ·
                refine ⟨12580293683674915573726421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8386862455783277049150947 12580293683674915573726421)
                ·
                  refine ⟨294850633211130833759213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12580293683674915573726421 294850633211130833759213)
                  ·
                    rfl

theorem cell23_5167976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_5167976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5167976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5167976 prefixEnd_5167976 := by exact prefixLift 5167976
  have htrace : WordTrace (prefixWord ++ tailWord_5167976) baseStart_5167976 baseEnd_5167976 := by
    simpa [prefixWord, tailWord_5167976, baseEnd_5167976] using wordTrace_append hprefix tailTrace_5167976
  have hstable : (prefixWord ++ tailWord_5167976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5167976).length < 2 ^ (prefixWord ++ tailWord_5167976).sum := by decide
  have hdescent : baseEnd_5167976 < baseStart_5167976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5167976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168019 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 7, 4]
def baseStart_5168019 : Nat := 118140960795 + 5168019 * 2 ^ 59
def prefixEnd_5168019 : Nat := 4983230072969 + 3 ^ 40 * 5168019 * 2
def baseEnd_5168019 : Nat := 884559259522773611865073

theorem tailTrace_5168019 : CollatzResearch.WordTrace tailWord_5168019 prefixEnd_5168019 884559259522773611865073 := by
  unfold tailWord_5168019
  simp only [CollatzResearch.WordTrace]
  refine ⟨188493138264157265220755111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125662092176104843480503407 188493138264157265220755111)
  ·
    refine ⟨282739707396235897831132667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188493138264157265220755111 282739707396235897831132667)
    ·
      refine ⟨424109561094353846746699001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282739707396235897831132667 424109561094353846746699001)
      ·
        refine ⟨318082170820765385060024251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424109561094353846746699001 318082170820765385060024251)
        ·
          refine ⟨477123256231148077590036377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318082170820765385060024251 477123256231148077590036377)
          ·
            refine ⟨357842442173361058192527283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477123256231148077590036377 357842442173361058192527283)
            ·
              refine ⟨536763663260041587288790925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357842442173361058192527283 536763663260041587288790925)
              ·
                refine ⟨201286373722515595233296597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536763663260041587288790925 201286373722515595233296597)
                ·
                  refine ⟨4717649384121459263280389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 201286373722515595233296597 4717649384121459263280389)
                  ·
                    refine ⟨884559259522773611865073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4717649384121459263280389 884559259522773611865073)
                    ·
                      rfl

theorem cell23_5168019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 4].length) (baseStart_5168019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168019 prefixEnd_5168019 := by exact prefixLift 5168019
  have htrace : WordTrace (prefixWord ++ tailWord_5168019) baseStart_5168019 baseEnd_5168019 := by
    simpa [prefixWord, tailWord_5168019, baseEnd_5168019] using wordTrace_append hprefix tailTrace_5168019
  have hstable : (prefixWord ++ tailWord_5168019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168019).length < 2 ^ (prefixWord ++ tailWord_5168019).sum := by decide
  have hdescent : baseEnd_5168019 < baseStart_5168019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168029 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5168029 : Nat := 118140960795 + 5168029 * 2 ^ 59
def prefixEnd_5168029 : Nat := 4983230072969 + 3 ^ 40 * 5168029 * 2
def baseEnd_5168029 : Nat := 2653682913374865796470173

theorem tailTrace_5168029 : CollatzResearch.WordTrace tailWord_5168029 prefixEnd_5168029 2653682913374865796470173 := by
  unfold tailWord_5168029
  simp only [CollatzResearch.WordTrace]
  refine ⟨188493502994121036928619141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125662335329414024619079427 188493502994121036928619141)
  ·
    refine ⟨35342531811397694424116089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188493502994121036928619141 35342531811397694424116089)
    ·
      refine ⟨26506898858548270818087067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35342531811397694424116089 26506898858548270818087067)
      ·
        refine ⟨39760348287822406227130601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26506898858548270818087067 39760348287822406227130601)
        ·
          refine ⟨29820261215866804670347951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39760348287822406227130601 29820261215866804670347951)
          ·
            refine ⟨44730391823800207005521927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29820261215866804670347951 44730391823800207005521927)
            ·
              refine ⟨67095587735700310508282891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44730391823800207005521927 67095587735700310508282891)
              ·
                refine ⟨100643381603550465762424337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67095587735700310508282891 100643381603550465762424337)
                ·
                  refine ⟨75482536202662849321818253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100643381603550465762424337 75482536202662849321818253)
                  ·
                    refine ⟨28305951075998568495681845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75482536202662849321818253 28305951075998568495681845)
                    ·
                      refine ⟨2653682913374865796470173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28305951075998568495681845 2653682913374865796470173)
                      ·
                        rfl

theorem cell23_5168029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5168029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168029 prefixEnd_5168029 := by exact prefixLift 5168029
  have htrace : WordTrace (prefixWord ++ tailWord_5168029) baseStart_5168029 baseEnd_5168029 := by
    simpa [prefixWord, tailWord_5168029, baseEnd_5168029] using wordTrace_append hprefix tailTrace_5168029
  have hstable : (prefixWord ++ tailWord_5168029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168029).length < 2 ^ (prefixWord ++ tailWord_5168029).sum := by decide
  have hdescent : baseEnd_5168029 < baseStart_5168029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168036 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_5168036 : Nat := 118140960795 + 5168036 * 2 ^ 59
def prefixEnd_5168036 : Nat := 4983230072969 + 3 ^ 40 * 5168036 * 2
def baseEnd_5168036 : Nat := 884562169246482423027547

theorem tailTrace_5168036 : CollatzResearch.WordTrace tailWord_5168036 prefixEnd_5168036 884562169246482423027547 := by
  unfold tailWord_5168036
  simp only [CollatzResearch.WordTrace]
  refine ⟨94246879152547838562061981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125662505536730451416082641 94246879152547838562061981)
  ·
    refine ⟨35342579682205439460773243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94246879152547838562061981 35342579682205439460773243)
    ·
      refine ⟨53013869523308159191159865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35342579682205439460773243 53013869523308159191159865)
      ·
        refine ⟨39760402142481119393369899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53013869523308159191159865 39760402142481119393369899)
        ·
          refine ⟨59640603213721679090054849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39760402142481119393369899 59640603213721679090054849)
          ·
            refine ⟨44730452410291259317541137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59640603213721679090054849 44730452410291259317541137)
            ·
              refine ⟨33547839307718444488155853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44730452410291259317541137 33547839307718444488155853)
              ·
                refine ⟨12580439740394416683058445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33547839307718444488155853 12580439740394416683058445)
                ·
                  refine ⟨4717664902647906256146917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12580439740394416683058445 4717664902647906256146917)
                  ·
                    refine ⟨884562169246482423027547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4717664902647906256146917 884562169246482423027547)
                    ·
                      rfl

theorem cell23_5168036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_5168036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168036 prefixEnd_5168036 := by exact prefixLift 5168036
  have htrace : WordTrace (prefixWord ++ tailWord_5168036) baseStart_5168036 baseEnd_5168036 := by
    simpa [prefixWord, tailWord_5168036, baseEnd_5168036] using wordTrace_append hprefix tailTrace_5168036
  have hstable : (prefixWord ++ tailWord_5168036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168036).length < 2 ^ (prefixWord ++ tailWord_5168036).sum := by decide
  have hdescent : baseEnd_5168036 < baseStart_5168036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168103 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5168103 : Nat := 118140960795 + 5168103 * 2 ^ 59
def prefixEnd_5168103 : Nat := 4983230072969 + 3 ^ 40 * 5168103 * 2
def baseEnd_5168103 : Nat := 2653720910943298506944833

theorem tailTrace_5168103 : CollatzResearch.WordTrace tailWord_5168103 prefixEnd_5168103 2653720910943298506944833 := by
  unfold tailWord_5168103
  simp only [CollatzResearch.WordTrace]
  refine ⟨188496201995852947566812963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125664134663901965044541975 188496201995852947566812963)
  ·
    refine ⟨282744302993779421350219445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188496201995852947566812963 282744302993779421350219445)
    ·
      refine ⟨26507278405666820751583073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 282744302993779421350219445 26507278405666820751583073)
      ·
        refine ⟨19880458804250115563687305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26507278405666820751583073 19880458804250115563687305)
        ·
          refine ⟨14910344103187586672765479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19880458804250115563687305 14910344103187586672765479)
          ·
            refine ⟨22365516154781380009148219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14910344103187586672765479 22365516154781380009148219)
            ·
              refine ⟨33548274232172070013722329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22365516154781380009148219 33548274232172070013722329)
              ·
                refine ⟨25161205674129052510291747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33548274232172070013722329 25161205674129052510291747)
                ·
                  refine ⟨37741808511193578765437621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25161205674129052510291747 37741808511193578765437621)
                  ·
                    refine ⟨3538294547924398009259777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37741808511193578765437621 3538294547924398009259777)
                    ·
                      refine ⟨2653720910943298506944833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538294547924398009259777 2653720910943298506944833)
                      ·
                        rfl

theorem cell23_5168103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5168103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168103 prefixEnd_5168103 := by exact prefixLift 5168103
  have htrace : WordTrace (prefixWord ++ tailWord_5168103) baseStart_5168103 baseEnd_5168103 := by
    simpa [prefixWord, tailWord_5168103, baseEnd_5168103] using wordTrace_append hprefix tailTrace_5168103
  have hstable : (prefixWord ++ tailWord_5168103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168103).length < 2 ^ (prefixWord ++ tailWord_5168103).sum := by decide
  have hdescent : baseEnd_5168103 < baseStart_5168103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168113 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_5168113 : Nat := 118140960795 + 5168113 * 2 ^ 59
def prefixEnd_5168113 : Nat := 4983230072969 + 3 ^ 40 * 5168113 * 2
def baseEnd_5168113 : Nat := 884575348583281155939929

theorem tailTrace_5168113 : CollatzResearch.WordTrace tailWord_5168113 prefixEnd_5168113 884575348583281155939929 := by
  unfold tailWord_5168113
  simp only [CollatzResearch.WordTrace]
  refine ⟨188496566725816719274676993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125664377817211146183117995 188496566725816719274676993)
  ·
    refine ⟨141372425044362539456007745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188496566725816719274676993 141372425044362539456007745)
    ·
      refine ⟨106029318783271904592005809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141372425044362539456007745 106029318783271904592005809)
      ·
        refine ⟨79521989087453928444004357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106029318783271904592005809 79521989087453928444004357)
        ·
          refine ⟨14910372953897611583250817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79521989087453928444004357 14910372953897611583250817)
          ·
            refine ⟨11182779715423208687438113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910372953897611583250817 11182779715423208687438113)
            ·
              refine ⟨8387084786567406515578585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11182779715423208687438113 8387084786567406515578585)
              ·
                refine ⟨6290313589925554886683939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387084786567406515578585 6290313589925554886683939)
                ·
                  refine ⟨9435470384888332330025909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290313589925554886683939 9435470384888332330025909)
                  ·
                    refine ⟨884575348583281155939929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9435470384888332330025909 884575348583281155939929)
                    ·
                      rfl

theorem cell23_5168113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_5168113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168113 prefixEnd_5168113 := by exact prefixLift 5168113
  have htrace : WordTrace (prefixWord ++ tailWord_5168113) baseStart_5168113 baseEnd_5168113 := by
    simpa [prefixWord, tailWord_5168113, baseEnd_5168113] using wordTrace_append hprefix tailTrace_5168113
  have hstable : (prefixWord ++ tailWord_5168113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168113).length < 2 ^ (prefixWord ++ tailWord_5168113).sum := by decide
  have hdescent : baseEnd_5168113 < baseStart_5168113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168136 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_5168136 : Nat := 118140960795 + 5168136 * 2 ^ 59
def prefixEnd_5168136 : Nat := 4983230072969 + 3 ^ 40 * 5168136 * 2
def baseEnd_5168136 : Nat := 2653737855804896877832181

theorem tailTrace_5168136 : CollatzResearch.WordTrace tailWord_5168136 prefixEnd_5168136 2653737855804896877832181 := by
  unfold tailWord_5168136
  simp only [CollatzResearch.WordTrace]
  refine ⟨94248702802366697101382131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125664937069822262801842841 94248702802366697101382131)
  ·
    refine ⟨141373054203550045652073197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94248702802366697101382131 141373054203550045652073197)
    ·
      refine ⟨53014895326331267119527449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141373054203550045652073197 53014895326331267119527449)
      ·
        refine ⟨39761171494748450339645587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53014895326331267119527449 39761171494748450339645587)
        ·
          refine ⟨59641757242122675509468381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39761171494748450339645587 59641757242122675509468381)
          ·
            refine ⟨22365658965796003316050643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59641757242122675509468381 22365658965796003316050643)
            ·
              refine ⟨33548488448694004974075965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22365658965796003316050643 33548488448694004974075965)
              ·
                refine ⟨12580683168260251865278487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33548488448694004974075965 12580683168260251865278487)
                ·
                  refine ⟨18871024752390377797917731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12580683168260251865278487 18871024752390377797917731)
                  ·
                    refine ⟨28306537128585566696876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18871024752390377797917731 28306537128585566696876597)
                    ·
                      refine ⟨2653737855804896877832181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28306537128585566696876597 2653737855804896877832181)
                      ·
                        rfl

theorem cell23_5168136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_5168136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168136 prefixEnd_5168136 := by exact prefixLift 5168136
  have htrace : WordTrace (prefixWord ++ tailWord_5168136) baseStart_5168136 baseEnd_5168136 := by
    simpa [prefixWord, tailWord_5168136, baseEnd_5168136] using wordTrace_append hprefix tailTrace_5168136
  have hstable : (prefixWord ++ tailWord_5168136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168136).length < 2 ^ (prefixWord ++ tailWord_5168136).sum := by decide
  have hdescent : baseEnd_5168136 < baseStart_5168136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168139 : List Nat := [1, 1, 1, 1, 6, 2, 11]
def baseStart_5168139 : Nat := 118140960795 + 5168139 * 2 ^ 59
def prefixEnd_5168139 : Nat := 4983230072969 + 3 ^ 40 * 5168139 * 2
def baseEnd_5168139 : Nat := 32762214768479757606107

theorem tailTrace_5168139 : CollatzResearch.WordTrace tailWord_5168139 prefixEnd_5168139 32762214768479757606107 := by
  unfold tailWord_5168139
  simp only [CollatzResearch.WordTrace]
  refine ⟨188497515023722525715123471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125665010015815017143415647 188497515023722525715123471)
  ·
    refine ⟨282746272535583788572685207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188497515023722525715123471 282746272535583788572685207)
    ·
      refine ⟨424119408803375682859027811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282746272535583788572685207 424119408803375682859027811)
      ·
        refine ⟨636179113205063524288541717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424119408803375682859027811 636179113205063524288541717)
        ·
          refine ⟨29820895931487352701025393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 636179113205063524288541717 29820895931487352701025393)
          ·
            refine ⟨22365671948615514525769045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29820895931487352701025393 22365671948615514525769045)
            ·
              refine ⟨32762214768479757606107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22365671948615514525769045 32762214768479757606107)
              ·
                rfl

theorem cell23_5168139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 11].length) (baseStart_5168139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168139 prefixEnd_5168139 := by exact prefixLift 5168139
  have htrace : WordTrace (prefixWord ++ tailWord_5168139) baseStart_5168139 baseEnd_5168139 := by
    simpa [prefixWord, tailWord_5168139, baseEnd_5168139] using wordTrace_append hprefix tailTrace_5168139
  have hstable : (prefixWord ++ tailWord_5168139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168139).length < 2 ^ (prefixWord ++ tailWord_5168139).sum := by decide
  have hdescent : baseEnd_5168139 < baseStart_5168139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168167 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5168167 : Nat := 118140960795 + 5168167 * 2 ^ 59
def prefixEnd_5168167 : Nat := 4983230072969 + 3 ^ 40 * 5168167 * 2
def baseEnd_5168167 : Nat := 2653753773705186256544539

theorem tailTrace_5168167 : CollatzResearch.WordTrace tailWord_5168167 prefixEnd_5168167 2653753773705186256544539 := by
  unfold tailWord_5168167
  simp only [CollatzResearch.WordTrace]
  refine ⟨188498536267621086497142755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125665690845080724331428503 188498536267621086497142755)
  ·
    refine ⟨282747804401431629745714133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188498536267621086497142755 282747804401431629745714133)
    ·
      refine ⟨6626901665658553822165175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 282747804401431629745714133 6626901665658553822165175)
      ·
        refine ⟨9940352498487830733247763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6626901665658553822165175 9940352498487830733247763)
        ·
          refine ⟨14910528747731746099871645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940352498487830733247763 14910528747731746099871645)
          ·
            refine ⟨5591448280399404787451867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14910528747731746099871645 5591448280399404787451867)
            ·
              refine ⟨8387172420599107181177801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591448280399404787451867 8387172420599107181177801)
              ·
                refine ⟨6290379315449330385883351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387172420599107181177801 6290379315449330385883351)
                ·
                  refine ⟨9435568973173995578825027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6290379315449330385883351 9435568973173995578825027)
                  ·
                    refine ⟨14153353459760993368237541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9435568973173995578825027 14153353459760993368237541)
                    ·
                      refine ⟨2653753773705186256544539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14153353459760993368237541 2653753773705186256544539)
                      ·
                        rfl

theorem cell23_5168167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5168167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168167 prefixEnd_5168167 := by exact prefixLift 5168167
  have htrace : WordTrace (prefixWord ++ tailWord_5168167) baseStart_5168167 baseEnd_5168167 := by
    simpa [prefixWord, tailWord_5168167, baseEnd_5168167] using wordTrace_append hprefix tailTrace_5168167
  have hstable : (prefixWord ++ tailWord_5168167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168167).length < 2 ^ (prefixWord ++ tailWord_5168167).sum := by decide
  have hdescent : baseEnd_5168167 < baseStart_5168167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168170 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5168170 : Nat := 118140960795 + 5168170 * 2 ^ 59
def prefixEnd_5168170 : Nat := 4983230072969 + 3 ^ 40 * 5168170 * 2
def baseEnd_5168170 : Nat := 2653755314147149744807025

theorem tailTrace_5168170 : CollatzResearch.WordTrace tailWord_5168170 prefixEnd_5168170 2653755314147149744807025 := by
  unfold tailWord_5168170
  simp only [CollatzResearch.WordTrace]
  refine ⟨47124661421652554502375491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125665763791073478673001309 47124661421652554502375491)
  ·
    refine ⟨70686992132478831753563237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47124661421652554502375491 70686992132478831753563237)
    ·
      refine ⟨13253811024839780953793107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70686992132478831753563237 13253811024839780953793107)
      ·
        refine ⟨19880716537259671430689661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13253811024839780953793107 19880716537259671430689661)
        ·
          refine ⟨7455268701472376786508623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19880716537259671430689661 7455268701472376786508623)
          ·
            refine ⟨11182903052208565179762935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455268701472376786508623 11182903052208565179762935)
            ·
              refine ⟨16774354578312847769644403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182903052208565179762935 16774354578312847769644403)
              ·
                refine ⟨25161531867469271654466605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16774354578312847769644403 25161531867469271654466605)
                ·
                  refine ⟨9435574450300976870424977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25161531867469271654466605 9435574450300976870424977)
                  ·
                    refine ⟨7076680837725732652818733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9435574450300976870424977 7076680837725732652818733)
                    ·
                      refine ⟨2653755314147149744807025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7076680837725732652818733 2653755314147149744807025)
                      ·
                        rfl

theorem cell23_5168170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5168170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168170 prefixEnd_5168170 := by exact prefixLift 5168170
  have htrace : WordTrace (prefixWord ++ tailWord_5168170) baseStart_5168170 baseEnd_5168170 := by
    simpa [prefixWord, tailWord_5168170, baseEnd_5168170] using wordTrace_append hprefix tailTrace_5168170
  have hstable : (prefixWord ++ tailWord_5168170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168170).length < 2 ^ (prefixWord ++ tailWord_5168170).sum := by decide
  have hdescent : baseEnd_5168170 < baseStart_5168170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168180 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5168180 : Nat := 118140960795 + 5168180 * 2 ^ 59
def prefixEnd_5168180 : Nat := 4983230072969 + 3 ^ 40 * 5168180 * 2
def baseEnd_5168180 : Nat := 2653760448953694705681979

theorem tailTrace_5168180 : CollatzResearch.WordTrace tailWord_5168180 prefixEnd_5168180 2653760448953694705681979 := by
  unfold tailWord_5168180
  simp only [CollatzResearch.WordTrace]
  refine ⟨94249505208286994858682997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125666006944382659811577329 94249505208286994858682997)
  ·
    refine ⟨8835891113276905768001531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94249505208286994858682997 8835891113276905768001531)
    ·
      refine ⟨13253836669915358652002297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8835891113276905768001531 13253836669915358652002297)
      ·
        refine ⟨9940377502436518989001723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253836669915358652002297 9940377502436518989001723)
        ·
          refine ⟨14910566253654778483502585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9940377502436518989001723 14910566253654778483502585)
          ·
            refine ⟨11182924690241083862626939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910566253654778483502585 11182924690241083862626939)
            ·
              refine ⟨16774387035361625793940409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182924690241083862626939 16774387035361625793940409)
              ·
                refine ⟨12580790276521219345455307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16774387035361625793940409 12580790276521219345455307)
                ·
                  refine ⟨18871185414781829018182961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12580790276521219345455307 18871185414781829018182961)
                  ·
                    refine ⟨14153389061086371763637221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18871185414781829018182961 14153389061086371763637221)
                    ·
                      refine ⟨2653760448953694705681979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14153389061086371763637221 2653760448953694705681979)
                      ·
                        rfl

theorem cell23_5168180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5168180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168180 prefixEnd_5168180 := by exact prefixLift 5168180
  have htrace : WordTrace (prefixWord ++ tailWord_5168180) baseStart_5168180 baseEnd_5168180 := by
    simpa [prefixWord, tailWord_5168180, baseEnd_5168180] using wordTrace_append hprefix tailTrace_5168180
  have hstable : (prefixWord ++ tailWord_5168180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168180).length < 2 ^ (prefixWord ++ tailWord_5168180).sum := by decide
  have hdescent : baseEnd_5168180 < baseStart_5168180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168200 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_5168200 : Nat := 118140960795 + 5168200 * 2 ^ 59
def prefixEnd_5168200 : Nat := 4983230072969 + 3 ^ 40 * 5168200 * 2
def baseEnd_5168200 : Nat := 2653770718566784627431887

theorem tailTrace_5168200 : CollatzResearch.WordTrace tailWord_5168200 prefixEnd_5168200 2653770718566784627431887 := by
  unfold tailWord_5168200
  simp only [CollatzResearch.WordTrace]
  refine ⟨94249869938250766566547027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125666493251001022088729369 94249869938250766566547027)
  ·
    refine ⟨141374804907376149849820541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94249869938250766566547027 141374804907376149849820541)
    ·
      refine ⟨53015551840266056193682703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141374804907376149849820541 53015551840266056193682703)
      ·
        refine ⟨79523327760399084290524055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53015551840266056193682703 79523327760399084290524055)
        ·
          refine ⟨119284991640598626435786083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79523327760399084290524055 119284991640598626435786083)
          ·
            refine ⟨178927487460897939653679125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119284991640598626435786083 178927487460897939653679125)
            ·
              refine ⟨8387225974729590921266209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 178927487460897939653679125 8387225974729590921266209)
              ·
                refine ⟨6290419481047193190949657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8387225974729590921266209 6290419481047193190949657)
                ·
                  refine ⟨4717814610785394893212243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290419481047193190949657 4717814610785394893212243)
                  ·
                    refine ⟨7076721916178092339818365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4717814610785394893212243 7076721916178092339818365)
                    ·
                      refine ⟨2653770718566784627431887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7076721916178092339818365 2653770718566784627431887)
                      ·
                        rfl

theorem cell23_5168200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_5168200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168200 prefixEnd_5168200 := by exact prefixLift 5168200
  have htrace : WordTrace (prefixWord ++ tailWord_5168200) baseStart_5168200 baseEnd_5168200 := by
    simpa [prefixWord, tailWord_5168200, baseEnd_5168200] using wordTrace_append hprefix tailTrace_5168200
  have hstable : (prefixWord ++ tailWord_5168200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168200).length < 2 ^ (prefixWord ++ tailWord_5168200).sum := by decide
  have hdescent : baseEnd_5168200 < baseStart_5168200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168206 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_5168206 : Nat := 118140960795 + 5168206 * 2 ^ 59
def prefixEnd_5168206 : Nat := 4983230072969 + 3 ^ 40 * 5168206 * 2
def baseEnd_5168206 : Nat := 2653773799450711603956859

theorem tailTrace_5168206 : CollatzResearch.WordTrace tailWord_5168206 prefixEnd_5168206 2653773799450711603956859 := by
  unfold tailWord_5168206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23562494839309974519726559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125666639142986530771874981 23562494839309974519726559)
  ·
    refine ⟨35343742258964961779589839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23562494839309974519726559 35343742258964961779589839)
    ·
      refine ⟨53015613388447442669384759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35343742258964961779589839 53015613388447442669384759)
      ·
        refine ⟨79523420082671164004077139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53015613388447442669384759 79523420082671164004077139)
        ·
          refine ⟨119285130124006746006115709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79523420082671164004077139 119285130124006746006115709)
          ·
            refine ⟨44731923796502529752293391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119285130124006746006115709 44731923796502529752293391)
            ·
              refine ⟨67097885694753794628440087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44731923796502529752293391 67097885694753794628440087)
              ·
                refine ⟨100646828542130691942660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67097885694753794628440087 100646828542130691942660131)
                ·
                  refine ⟨150970242813196037913990197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100646828542130691942660131 150970242813196037913990197)
                  ·
                    refine ⟨14153460263737128554436581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150970242813196037913990197 14153460263737128554436581)
                    ·
                      refine ⟨2653773799450711603956859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14153460263737128554436581 2653773799450711603956859)
                      ·
                        rfl

theorem cell23_5168206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_5168206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168206 prefixEnd_5168206 := by exact prefixLift 5168206
  have htrace : WordTrace (prefixWord ++ tailWord_5168206) baseStart_5168206 baseEnd_5168206 := by
    simpa [prefixWord, tailWord_5168206, baseEnd_5168206] using wordTrace_append hprefix tailTrace_5168206
  have hstable : (prefixWord ++ tailWord_5168206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168206).length < 2 ^ (prefixWord ++ tailWord_5168206).sum := by decide
  have hdescent : baseEnd_5168206 < baseStart_5168206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168210 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_5168210 : Nat := 118140960795 + 5168210 * 2 ^ 59
def prefixEnd_5168210 : Nat := 4983230072969 + 3 ^ 40 * 5168210 * 2
def baseEnd_5168210 : Nat := 2653775853373329588306841

theorem tailTrace_5168210 : CollatzResearch.WordTrace tailWord_5168210 prefixEnd_5168210 2653775853373329588306841 := by
  unfold tailWord_5168210
  simp only [CollatzResearch.WordTrace]
  refine ⟨47125026151616326210239521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125666736404310203227305389 47125026151616326210239521)
  ·
    refine ⟨35343769613712244657679641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47125026151616326210239521 35343769613712244657679641)
    ·
      refine ⟨26507827210284183493259731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35343769613712244657679641 26507827210284183493259731)
      ·
        refine ⟨39761740815426275239889597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26507827210284183493259731 39761740815426275239889597)
        ·
          refine ⟨14910652805784853214958599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39761740815426275239889597 14910652805784853214958599)
          ·
            refine ⟨22365979208677279822437899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14910652805784853214958599 22365979208677279822437899)
            ·
              refine ⟨33548968813015919733656849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22365979208677279822437899 33548968813015919733656849)
              ·
                refine ⟨25161726609761939800242637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33548968813015919733656849 25161726609761939800242637)
                ·
                  refine ⟨9435647478660727425090989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25161726609761939800242637 9435647478660727425090989)
                  ·
                    refine ⟨3538367804497772784409121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9435647478660727425090989 3538367804497772784409121)
                    ·
                      refine ⟨2653775853373329588306841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538367804497772784409121 2653775853373329588306841)
                      ·
                        rfl

theorem cell23_5168210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_5168210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168210 prefixEnd_5168210 := by exact prefixLift 5168210
  have htrace : WordTrace (prefixWord ++ tailWord_5168210) baseStart_5168210 baseEnd_5168210 := by
    simpa [prefixWord, tailWord_5168210, baseEnd_5168210] using wordTrace_append hprefix tailTrace_5168210
  have hstable : (prefixWord ++ tailWord_5168210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168210).length < 2 ^ (prefixWord ++ tailWord_5168210).sum := by decide
  have hdescent : baseEnd_5168210 < baseStart_5168210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168216 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_5168216 : Nat := 118140960795 + 5168216 * 2 ^ 59
def prefixEnd_5168216 : Nat := 4983230072969 + 3 ^ 40 * 5168216 * 2
def baseEnd_5168216 : Nat := 884592978085752188277271

theorem tailTrace_5168216 : CollatzResearch.WordTrace tailWord_5168216 prefixEnd_5168216 884592978085752188277271 := by
  unfold tailWord_5168216
  simp only [CollatzResearch.WordTrace]
  refine ⟨94250161722221783932838251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125666882296295711910451001 94250161722221783932838251)
  ·
    refine ⟨141375242583332675899257377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94250161722221783932838251 141375242583332675899257377)
    ·
      refine ⟨106031431937499506924443033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141375242583332675899257377 106031431937499506924443033)
      ·
        refine ⟨79523573953124630193332275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106031431937499506924443033 79523573953124630193332275)
        ·
          refine ⟨119285360929686945289998413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79523573953124630193332275 119285360929686945289998413)
          ·
            refine ⟨44732010348632604483749405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119285360929686945289998413 44732010348632604483749405)
            ·
              refine ⟨16774503880737226681406027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44732010348632604483749405 16774503880737226681406027)
              ·
                refine ⟨25161755821105840022109041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16774503880737226681406027 25161755821105840022109041)
                ·
                  refine ⟨18871316865829380016581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25161755821105840022109041 18871316865829380016581781)
                  ·
                    refine ⟨884592978085752188277271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18871316865829380016581781 884592978085752188277271)
                    ·
                      rfl

theorem cell23_5168216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_5168216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168216 prefixEnd_5168216 := by exact prefixLift 5168216
  have htrace : WordTrace (prefixWord ++ tailWord_5168216) baseStart_5168216 baseEnd_5168216 := by
    simpa [prefixWord, tailWord_5168216, baseEnd_5168216] using wordTrace_append hprefix tailTrace_5168216
  have hstable : (prefixWord ++ tailWord_5168216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168216).length < 2 ^ (prefixWord ++ tailWord_5168216).sum := by decide
  have hdescent : baseEnd_5168216 < baseStart_5168216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168236 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_5168236 : Nat := 118140960795 + 5168236 * 2 ^ 59
def prefixEnd_5168236 : Nat := 4983230072969 + 3 ^ 40 * 5168236 * 2
def baseEnd_5168236 : Nat := 2653789203870346486581721

theorem tailTrace_5168236 : CollatzResearch.WordTrace tailWord_5168236 prefixEnd_5168236 2653789203870346486581721 := by
  unfold tailWord_5168236
  simp only [CollatzResearch.WordTrace]
  refine ⟨94250526452185555640702281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125667368602914074187603041 94250526452185555640702281)
  ·
    refine ⟨70687894839139166730526711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94250526452185555640702281 70687894839139166730526711)
    ·
      refine ⟨106031842258708750095790067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70687894839139166730526711 106031842258708750095790067)
      ·
        refine ⟨159047763388063125143685101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106031842258708750095790067 159047763388063125143685101)
        ·
          refine ⟨59642911270523671928881913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159047763388063125143685101 59642911270523671928881913)
          ·
            refine ⟨44732183452892753946661435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59642911270523671928881913 44732183452892753946661435)
            ·
              refine ⟨67098275179339130919992153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44732183452892753946661435 67098275179339130919992153)
              ·
                refine ⟨50323706384504348189994115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67098275179339130919992153 50323706384504348189994115)
                ·
                  refine ⟨75485559576756522284991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50323706384504348189994115 75485559576756522284991173)
                  ·
                    refine ⟨14153542420641847928435845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75485559576756522284991173 14153542420641847928435845)
                    ·
                      refine ⟨2653789203870346486581721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14153542420641847928435845 2653789203870346486581721)
                      ·
                        rfl

theorem cell23_5168236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_5168236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168236 prefixEnd_5168236 := by exact prefixLift 5168236
  have htrace : WordTrace (prefixWord ++ tailWord_5168236) baseStart_5168236 baseEnd_5168236 := by
    simpa [prefixWord, tailWord_5168236, baseEnd_5168236] using wordTrace_append hprefix tailTrace_5168236
  have hstable : (prefixWord ++ tailWord_5168236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168236).length < 2 ^ (prefixWord ++ tailWord_5168236).sum := by decide
  have hdescent : baseEnd_5168236 < baseStart_5168236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168240 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2]
def baseStart_5168240 : Nat := 118140960795 + 5168240 * 2 ^ 59
def prefixEnd_5168240 : Nat := 4983230072969 + 3 ^ 40 * 5168240 * 2
def baseEnd_5168240 : Nat := 2653791257792964470931703

theorem tailTrace_5168240 : CollatzResearch.WordTrace tailWord_5168240 prefixEnd_5168240 2653791257792964470931703 := by
  unfold tailWord_5168240
  simp only [CollatzResearch.WordTrace]
  refine ⟨94250599398178309982275087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125667465864237746643033449 94250599398178309982275087)
  ·
    refine ⟨141375899097267464973412631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94250599398178309982275087 141375899097267464973412631)
    ·
      refine ⟨212063848645901197460118947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141375899097267464973412631 212063848645901197460118947)
      ·
        refine ⟨318095772968851796190178421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212063848645901197460118947 318095772968851796190178421)
        ·
          refine ⟨29821478715829855892829227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318095772968851796190178421 29821478715829855892829227)
          ·
            refine ⟨44732218073744783839243841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29821478715829855892829227 44732218073744783839243841)
            ·
              refine ⟨33549163555308587879432881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44732218073744783839243841 33549163555308587879432881)
              ·
                refine ⟨25161872666481440909574661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33549163555308587879432881 25161872666481440909574661)
                ·
                  refine ⟨4717851124965270170545249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25161872666481440909574661 4717851124965270170545249)
                  ·
                    refine ⟨3538388343723952627908937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4717851124965270170545249 3538388343723952627908937)
                    ·
                      refine ⟨2653791257792964470931703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538388343723952627908937 2653791257792964470931703)
                      ·
                        rfl

theorem cell23_5168240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2].length) (baseStart_5168240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168240 prefixEnd_5168240 := by exact prefixLift 5168240
  have htrace : WordTrace (prefixWord ++ tailWord_5168240) baseStart_5168240 baseEnd_5168240 := by
    simpa [prefixWord, tailWord_5168240, baseEnd_5168240] using wordTrace_append hprefix tailTrace_5168240
  have hstable : (prefixWord ++ tailWord_5168240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168240).length < 2 ^ (prefixWord ++ tailWord_5168240).sum := by decide
  have hdescent : baseEnd_5168240 < baseStart_5168240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168257 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_5168257 : Nat := 118140960795 + 5168257 * 2 ^ 59
def prefixEnd_5168257 : Nat := 4983230072969 + 3 ^ 40 * 5168257 * 2
def baseEnd_5168257 : Nat := 2653799986964090904419125

theorem tailTrace_5168257 : CollatzResearch.WordTrace tailWord_5168257 prefixEnd_5168257 2653799986964090904419125 := by
  unfold tailWord_5168257
  simp only [CollatzResearch.WordTrace]
  refine ⟨188501818837295031867919025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125667879224863354578612683 188501818837295031867919025)
  ·
    refine ⟨141376364127971273900939269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188501818837295031867919025 141376364127971273900939269)
    ·
      refine ⟨26508068273994613856426113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141376364127971273900939269 26508068273994613856426113)
      ·
        refine ⟨19881051205495960392319585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26508068273994613856426113 19881051205495960392319585)
        ·
          refine ⟨14910788404121970294239689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19881051205495960392319585 14910788404121970294239689)
          ·
            refine ⟨11183091303091477720679767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14910788404121970294239689 11183091303091477720679767)
            ·
              refine ⟨16774636954637216581019651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11183091303091477720679767 16774636954637216581019651)
              ·
                refine ⟨25161955431955824871529477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16774636954637216581019651 25161955431955824871529477)
                ·
                  refine ⟨4717866643491717163411777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25161955431955824871529477 4717866643491717163411777)
                  ·
                    refine ⟨3538399982618787872558833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4717866643491717163411777 3538399982618787872558833)
                    ·
                      refine ⟨2653799986964090904419125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538399982618787872558833 2653799986964090904419125)
                      ·
                        rfl

theorem cell23_5168257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_5168257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168257 prefixEnd_5168257 := by exact prefixLift 5168257
  have htrace : WordTrace (prefixWord ++ tailWord_5168257) baseStart_5168257 baseEnd_5168257 := by
    simpa [prefixWord, tailWord_5168257, baseEnd_5168257] using wordTrace_append hprefix tailTrace_5168257
  have hstable : (prefixWord ++ tailWord_5168257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168257).length < 2 ^ (prefixWord ++ tailWord_5168257).sum := by decide
  have hdescent : baseEnd_5168257 < baseStart_5168257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168313 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5168313 : Nat := 118140960795 + 5168313 * 2 ^ 59
def prefixEnd_5168313 : Nat := 4983230072969 + 3 ^ 40 * 5168313 * 2
def baseEnd_5168313 : Nat := 2653828741880742685318867

theorem tailTrace_5168313 : CollatzResearch.WordTrace tailWord_5168313 prefixEnd_5168313 2653828741880742685318867 := by
  unfold tailWord_5168313
  simp only [CollatzResearch.WordTrace]
  refine ⟨188503861325092153431957593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125669240883394768954638395 188503861325092153431957593)
  ·
    refine ⟨141377895993819115073968195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188503861325092153431957593 141377895993819115073968195)
    ·
      refine ⟨212066843990728672610952293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141377895993819115073968195 212066843990728672610952293)
      ·
        refine ⟨39762533248261626114553555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212066843990728672610952293 39762533248261626114553555)
        ·
          refine ⟨59643799872392439171830333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39762533248261626114553555 59643799872392439171830333)
          ·
            refine ⟨22366424952147164689436375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59643799872392439171830333 22366424952147164689436375)
            ·
              refine ⟨33549637428220747034154563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22366424952147164689436375 33549637428220747034154563)
              ·
                refine ⟨50324456142331120551231845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33549637428220747034154563 50324456142331120551231845)
                ·
                  refine ⟨9435835526687085103355971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50324456142331120551231845 9435835526687085103355971)
                  ·
                    refine ⟨14153753290030627655033957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9435835526687085103355971 14153753290030627655033957)
                    ·
                      refine ⟨2653828741880742685318867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14153753290030627655033957 2653828741880742685318867)
                      ·
                        rfl

theorem cell23_5168313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5168313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168313 prefixEnd_5168313 := by exact prefixLift 5168313
  have htrace : WordTrace (prefixWord ++ tailWord_5168313) baseStart_5168313 baseEnd_5168313 := by
    simpa [prefixWord, tailWord_5168313, baseEnd_5168313] using wordTrace_append hprefix tailTrace_5168313
  have hstable : (prefixWord ++ tailWord_5168313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168313).length < 2 ^ (prefixWord ++ tailWord_5168313).sum := by decide
  have hdescent : baseEnd_5168313 < baseStart_5168313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168323 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 3, 4]
def baseStart_5168323 : Nat := 118140960795 + 5168323 * 2 ^ 59
def prefixEnd_5168323 : Nat := 4983230072969 + 3 ^ 40 * 5168323 * 2
def baseEnd_5168323 : Nat := 884611292229095882064607

theorem tailTrace_5168323 : CollatzResearch.WordTrace tailWord_5168323 prefixEnd_5168323 884611292229095882064607 := by
  unfold tailWord_5168323
  simp only [CollatzResearch.WordTrace]
  refine ⟨188504226055055925139821623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125669484036703950093214415 188504226055055925139821623)
  ·
    refine ⟨282756339082583887709732435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188504226055055925139821623 282756339082583887709732435)
    ·
      refine ⟨424134508623875831564598653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282756339082583887709732435 424134508623875831564598653)
      ·
        refine ⟨159050440733953436836724495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424134508623875831564598653 159050440733953436836724495)
        ·
          refine ⟨238575661100930155255086743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159050440733953436836724495 238575661100930155255086743)
          ·
            refine ⟨357863491651395232882630115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238575661100930155255086743 357863491651395232882630115)
            ·
              refine ⟨536795237477092849323945173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357863491651395232882630115 536795237477092849323945173)
              ·
                refine ⟨12581138378369363656029965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 536795237477092849323945173 12581138378369363656029965)
                ·
                  refine ⟨4717926891888511371011237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12581138378369363656029965 4717926891888511371011237)
                  ·
                    refine ⟨884611292229095882064607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4717926891888511371011237 884611292229095882064607)
                    ·
                      rfl

theorem cell23_5168323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 4].length) (baseStart_5168323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168323 prefixEnd_5168323 := by exact prefixLift 5168323
  have htrace : WordTrace (prefixWord ++ tailWord_5168323) baseStart_5168323 baseEnd_5168323 := by
    simpa [prefixWord, tailWord_5168323, baseEnd_5168323] using wordTrace_append hprefix tailTrace_5168323
  have hstable : (prefixWord ++ tailWord_5168323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168323).length < 2 ^ (prefixWord ++ tailWord_5168323).sum := by decide
  have hdescent : baseEnd_5168323 < baseStart_5168323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168383 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 3, 5]
def baseStart_5168383 : Nat := 118140960795 + 5168383 * 2 ^ 59
def prefixEnd_5168383 : Nat := 4983230072969 + 3 ^ 40 * 5168383 * 2
def baseEnd_5168383 : Nat := 884621561842185803814515

theorem tailTrace_5168383 : CollatzResearch.WordTrace tailWord_5168383 prefixEnd_5168383 884621561842185803814515 := by
  unfold tailWord_5168383
  simp only [CollatzResearch.WordTrace]
  refine ⟨188506414434838555387005803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125670942956559036924670535 188506414434838555387005803)
  ·
    refine ⟨282759621652257833080508705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188506414434838555387005803 282759621652257833080508705)
    ·
      refine ⟨212069716239193374810381529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282759621652257833080508705 212069716239193374810381529)
      ·
        refine ⟨159052287179395031107786147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212069716239193374810381529 159052287179395031107786147)
        ·
          refine ⟨238578430769092546661679221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159052287179395031107786147 238578430769092546661679221)
          ·
            refine ⟨22366727884602426249532427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238578430769092546661679221 22366727884602426249532427)
            ·
              refine ⟨33550091826903639374298641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22366727884602426249532427 33550091826903639374298641)
              ·
                refine ⟨25162568870177729530723981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33550091826903639374298641 25162568870177729530723981)
                ·
                  refine ⟨9435963326316648574021493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25162568870177729530723981 9435963326316648574021493)
                  ·
                    refine ⟨884621561842185803814515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9435963326316648574021493 884621561842185803814515)
                    ·
                      rfl

theorem cell23_5168383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_5168383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168383 prefixEnd_5168383 := by exact prefixLift 5168383
  have htrace : WordTrace (prefixWord ++ tailWord_5168383) baseStart_5168383 baseEnd_5168383 := by
    simpa [prefixWord, tailWord_5168383, baseEnd_5168383] using wordTrace_append hprefix tailTrace_5168383
  have hstable : (prefixWord ++ tailWord_5168383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168383).length < 2 ^ (prefixWord ++ tailWord_5168383).sum := by decide
  have hdescent : baseEnd_5168383 < baseStart_5168383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168460 : List Nat := [2, 2, 1, 3, 2, 2, 4, 7]
def baseStart_5168460 : Nat := 118140960795 + 5168460 * 2 ^ 59
def prefixEnd_5168460 : Nat := 4983230072969 + 3 ^ 40 * 5168460 * 2
def baseEnd_5168460 : Nat := 98292749019887170747433

theorem tailTrace_5168460 : CollatzResearch.WordTrace tailWord_5168460 prefixEnd_5168460 98292749019887170747433 := by
  unfold tailWord_5168460
  simp only [CollatzResearch.WordTrace]
  refine ⟨94254611427779798768779417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125672815237039731691705889 94254611427779798768779417)
  ·
    refine ⟨70690958570834849076584563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94254611427779798768779417 70690958570834849076584563)
    ·
      refine ⟨106036437856252273614876845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70690958570834849076584563 106036437856252273614876845)
      ·
        refine ⟨39763664196094602605578817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106036437856252273614876845 39763664196094602605578817)
        ·
          refine ⟨29822748147070951954184113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39763664196094602605578817 29822748147070951954184113)
          ·
            refine ⟨22367061110303213965638085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29822748147070951954184113 22367061110303213965638085)
            ·
              refine ⟨4193823958181852618557141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22367061110303213965638085 4193823958181852618557141)
              ·
                refine ⟨98292749019887170747433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4193823958181852618557141 98292749019887170747433)
                ·
                  rfl

theorem cell23_5168460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 7].length) (baseStart_5168460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168460 prefixEnd_5168460 := by exact prefixLift 5168460
  have htrace : WordTrace (prefixWord ++ tailWord_5168460) baseStart_5168460 baseEnd_5168460 := by
    simpa [prefixWord, tailWord_5168460, baseEnd_5168460] using wordTrace_append hprefix tailTrace_5168460
  have hstable : (prefixWord ++ tailWord_5168460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168460).length < 2 ^ (prefixWord ++ tailWord_5168460).sum := by decide
  have hdescent : baseEnd_5168460 < baseStart_5168460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168471 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 1, 2, 2]
def baseStart_5168471 : Nat := 118140960795 + 5168471 * 2 ^ 59
def prefixEnd_5168471 : Nat := 4983230072969 + 3 ^ 40 * 5168471 * 2
def baseEnd_5168471 : Nat := 2653909871824153067143141

theorem tailTrace_5168471 : CollatzResearch.WordTrace tailWord_5168471 prefixEnd_5168471 2653909871824153067143141 := by
  unfold tailWord_5168471
  simp only [CollatzResearch.WordTrace]
  refine ⟨188509624058519746416209267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125673082705679830944139511 188509624058519746416209267)
  ·
    refine ⟨282764436087779619624313901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188509624058519746416209267 282764436087779619624313901)
    ·
      refine ⟨106036663532917357359117713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282764436087779619624313901 106036663532917357359117713)
      ·
        refine ⟨79527497649688018019338285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106036663532917357359117713 79527497649688018019338285)
        ·
          refine ⟨29822811618633006757251857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79527497649688018019338285 29822811618633006757251857)
          ·
            refine ⟨22367108713974755067938893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29822811618633006757251857 22367108713974755067938893)
            ·
              refine ⟨8387665767740533150477085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22367108713974755067938893 8387665767740533150477085)
              ·
                refine ⟨3145374662902699931428907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8387665767740533150477085 3145374662902699931428907)
                ·
                  refine ⟨4718061994354049897143361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145374662902699931428907 4718061994354049897143361)
                  ·
                    refine ⟨3538546495765537422857521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718061994354049897143361 3538546495765537422857521)
                    ·
                      refine ⟨2653909871824153067143141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538546495765537422857521 2653909871824153067143141)
                      ·
                        rfl

theorem cell23_5168471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_5168471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168471 prefixEnd_5168471 := by exact prefixLift 5168471
  have htrace : WordTrace (prefixWord ++ tailWord_5168471) baseStart_5168471 baseEnd_5168471 := by
    simpa [prefixWord, tailWord_5168471, baseEnd_5168471] using wordTrace_append hprefix tailTrace_5168471
  have hstable : (prefixWord ++ tailWord_5168471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168471).length < 2 ^ (prefixWord ++ tailWord_5168471).sum := by decide
  have hdescent : baseEnd_5168471 < baseStart_5168471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168488 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5168488 : Nat := 118140960795 + 5168488 * 2 ^ 59
def prefixEnd_5168488 : Nat := 4983230072969 + 3 ^ 40 * 5168488 * 2
def baseEnd_5168488 : Nat := 2653918600995279500630563

theorem tailTrace_5168488 : CollatzResearch.WordTrace tailWord_5168488 prefixEnd_5168488 2653918600995279500630563 := by
  unfold tailWord_5168488
  simp only [CollatzResearch.WordTrace]
  refine ⟨94255122049729079159789059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125673496066305438879718745 94255122049729079159789059)
  ·
    refine ⟨141382683074593618739683589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94255122049729079159789059 141382683074593618739683589)
    ·
      refine ⟨26509253076486303513690673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141382683074593618739683589 26509253076486303513690673)
      ·
        refine ⟨19881939807364727635268005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26509253076486303513690673 19881939807364727635268005)
        ·
          refine ⟨3727863713880886431612751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19881939807364727635268005 3727863713880886431612751)
          ·
            refine ⟨5591795570821329647419127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727863713880886431612751 5591795570821329647419127)
            ·
              refine ⟨8387693356231994471128691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591795570821329647419127 8387693356231994471128691)
              ·
                refine ⟨12581540034347991706693037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8387693356231994471128691 12581540034347991706693037)
                ·
                  refine ⟨4718077512880496890009889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12581540034347991706693037 4718077512880496890009889)
                  ·
                    refine ⟨3538558134660372667507417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718077512880496890009889 3538558134660372667507417)
                    ·
                      refine ⟨2653918600995279500630563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538558134660372667507417 2653918600995279500630563)
                      ·
                        rfl

theorem cell23_5168488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5168488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168488 prefixEnd_5168488 := by exact prefixLift 5168488
  have htrace : WordTrace (prefixWord ++ tailWord_5168488) baseStart_5168488 baseEnd_5168488 := by
    simpa [prefixWord, tailWord_5168488, baseEnd_5168488] using wordTrace_append hprefix tailTrace_5168488
  have hstable : (prefixWord ++ tailWord_5168488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168488).length < 2 ^ (prefixWord ++ tailWord_5168488).sum := by decide
  have hdescent : baseEnd_5168488 < baseStart_5168488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168503 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 8]
def baseStart_5168503 : Nat := 118140960795 + 5168503 * 2 ^ 59
def prefixEnd_5168503 : Nat := 4983230072969 + 3 ^ 40 * 5168503 * 2
def baseEnd_5168503 : Nat := 884642101068365647314331

theorem tailTrace_5168503 : CollatzResearch.WordTrace tailWord_5168503 prefixEnd_5168503 884642101068365647314331 := by
  unfold tailWord_5168503
  simp only [CollatzResearch.WordTrace]
  refine ⟨188510791194403815881374163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125673860796269210587582775 188510791194403815881374163)
  ·
    refine ⟨282766186791605723822061245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188510791194403815881374163 282766186791605723822061245)
    ·
      refine ⟨106037320046852146433272967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282766186791605723822061245 106037320046852146433272967)
      ·
        refine ⟨159055980070278219649909451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106037320046852146433272967 159055980070278219649909451)
        ·
          refine ⟨238583970105417329474864177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159055980070278219649909451 238583970105417329474864177)
          ·
            refine ⟨178937977579062997106148133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238583970105417329474864177 178937977579062997106148133)
            ·
              refine ⟨33550870796074311957402775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178937977579062997106148133 33550870796074311957402775)
              ·
                refine ⟨50326306194111467936104163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33550870796074311957402775 50326306194111467936104163)
                ·
                  refine ⟨75489459291167201904156245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50326306194111467936104163 75489459291167201904156245)
                  ·
                    refine ⟨884642101068365647314331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75489459291167201904156245 884642101068365647314331)
                    ·
                      rfl

theorem cell23_5168503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_5168503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168503 prefixEnd_5168503 := by exact prefixLift 5168503
  have htrace : WordTrace (prefixWord ++ tailWord_5168503) baseStart_5168503 baseEnd_5168503 := by
    simpa [prefixWord, tailWord_5168503, baseEnd_5168503] using wordTrace_append hprefix tailTrace_5168503
  have hstable : (prefixWord ++ tailWord_5168503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168503).length < 2 ^ (prefixWord ++ tailWord_5168503).sum := by decide
  have hdescent : baseEnd_5168503 < baseStart_5168503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168553 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_5168553 : Nat := 118140960795 + 5168553 * 2 ^ 59
def prefixEnd_5168553 : Nat := 4983230072969 + 3 ^ 40 * 5168553 * 2
def baseEnd_5168553 : Nat := 2653951977237821746317763

theorem tailTrace_5168553 : CollatzResearch.WordTrace tailWord_5168553 prefixEnd_5168553 2653951977237821746317763 := by
  unfold tailWord_5168553
  simp only [CollatzResearch.WordTrace]
  refine ⟨188512614844222674420694313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125675076562815116280462875 188512614844222674420694313)
  ·
    refine ⟨141384461133167005815520735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188512614844222674420694313 141384461133167005815520735)
    ·
      refine ⟨212076691699750508723281103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141384461133167005815520735 212076691699750508723281103)
      ·
        refine ⟨318115037549625763084921655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212076691699750508723281103 318115037549625763084921655)
        ·
          refine ⟨477172556324438644627382483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318115037549625763084921655 477172556324438644627382483)
          ·
            refine ⟨715758834486657966941073725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477172556324438644627382483 715758834486657966941073725)
            ·
              refine ⟨268409562932496737602902647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715758834486657966941073725 268409562932496737602902647)
              ·
                refine ⟨402614344398745106404353971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268409562932496737602902647 402614344398745106404353971)
                ·
                  refine ⟨603921516598117659606530957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402614344398745106404353971 603921516598117659606530957)
                  ·
                    refine ⟨226470568724294122352449109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603921516598117659606530957 226470568724294122352449109)
                    ·
                      refine ⟨2653951977237821746317763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226470568724294122352449109 2653951977237821746317763)
                      ·
                        rfl

theorem cell23_5168553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_5168553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168553 prefixEnd_5168553 := by exact prefixLift 5168553
  have htrace : WordTrace (prefixWord ++ tailWord_5168553) baseStart_5168553 baseEnd_5168553 := by
    simpa [prefixWord, tailWord_5168553, baseEnd_5168553] using wordTrace_append hprefix tailTrace_5168553
  have hstable : (prefixWord ++ tailWord_5168553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168553).length < 2 ^ (prefixWord ++ tailWord_5168553).sum := by decide
  have hdescent : baseEnd_5168553 < baseStart_5168553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168557 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5168557 : Nat := 118140960795 + 5168557 * 2 ^ 59
def prefixEnd_5168557 : Nat := 4983230072969 + 3 ^ 40 * 5168557 * 2
def baseEnd_5168557 : Nat := 2653954031160439730667745

theorem tailTrace_5168557 : CollatzResearch.WordTrace tailWord_5168557 prefixEnd_5168557 2653954031160439730667745 := by
  unfold tailWord_5168557
  simp only [CollatzResearch.WordTrace]
  refine ⟨188512760736208183103839925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125675173824138788735893283 188512760736208183103839925)
  ·
    refine ⟨17673071319019517165984993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188512760736208183103839925 17673071319019517165984993)
    ·
      refine ⟨13254803489264637874488745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17673071319019517165984993 13254803489264637874488745)
      ·
        refine ⟨9941102616948478405866559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13254803489264637874488745 9941102616948478405866559)
        ·
          refine ⟨14911653925422717608799839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941102616948478405866559 14911653925422717608799839)
          ·
            refine ⟨22367480888134076413199759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14911653925422717608799839 22367480888134076413199759)
            ·
              refine ⟨33551221332201114619799639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22367480888134076413199759 33551221332201114619799639)
              ·
                refine ⟨50326831998301671929699459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33551221332201114619799639 50326831998301671929699459)
                ·
                  refine ⟨75490247997452507894549189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50326831998301671929699459 75490247997452507894549189)
                  ·
                    refine ⟨14154421499522345230227973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75490247997452507894549189 14154421499522345230227973)
                    ·
                      refine ⟨2653954031160439730667745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14154421499522345230227973 2653954031160439730667745)
                      ·
                        rfl

theorem cell23_5168557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5168557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168557 prefixEnd_5168557 := by exact prefixLift 5168557
  have htrace : WordTrace (prefixWord ++ tailWord_5168557) baseStart_5168557 baseEnd_5168557 := by
    simpa [prefixWord, tailWord_5168557, baseEnd_5168557] using wordTrace_append hprefix tailTrace_5168557
  have hstable : (prefixWord ++ tailWord_5168557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168557).length < 2 ^ (prefixWord ++ tailWord_5168557).sum := by decide
  have hdescent : baseEnd_5168557 < baseStart_5168557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168590 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_5168590 : Nat := 118140960795 + 5168590 * 2 ^ 59
def prefixEnd_5168590 : Nat := 4983230072969 + 3 ^ 40 * 5168590 * 2
def baseEnd_5168590 : Nat := 2653970976022038101555093

theorem tailTrace_5168590 : CollatzResearch.WordTrace tailWord_5168590 prefixEnd_5168590 2653970976022038101555093 := by
  unfold tailWord_5168590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23564245543136078717473903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125675976230059086493194149 23564245543136078717473903)
  ·
    refine ⟨35346368314704118076210855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23564245543136078717473903 35346368314704118076210855)
    ·
      refine ⟨53019552472056177114316283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35346368314704118076210855 53019552472056177114316283)
      ·
        refine ⟨79529328708084265671474425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53019552472056177114316283 79529328708084265671474425)
        ·
          refine ⟨59646996531063199253605819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79529328708084265671474425 59646996531063199253605819)
          ·
            refine ⟨89470494796594798880408729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59646996531063199253605819 89470494796594798880408729)
            ·
              refine ⟨67102871097446099160306547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89470494796594798880408729 67102871097446099160306547)
              ·
                refine ⟨100654306646169148740459821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67102871097446099160306547 100654306646169148740459821)
                ·
                  refine ⟨37745364992313430777672433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100654306646169148740459821 37745364992313430777672433)
                  ·
                    refine ⟨28309023744235073083254325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37745364992313430777672433 28309023744235073083254325)
                    ·
                      refine ⟨2653970976022038101555093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28309023744235073083254325 2653970976022038101555093)
                      ·
                        rfl

theorem cell23_5168590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_5168590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168590 prefixEnd_5168590 := by exact prefixLift 5168590
  have htrace : WordTrace (prefixWord ++ tailWord_5168590) baseStart_5168590 baseEnd_5168590 := by
    simpa [prefixWord, tailWord_5168590, baseEnd_5168590] using wordTrace_append hprefix tailTrace_5168590
  have hstable : (prefixWord ++ tailWord_5168590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168590).length < 2 ^ (prefixWord ++ tailWord_5168590).sum := by decide
  have hdescent : baseEnd_5168590 < baseStart_5168590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168637 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_5168637 : Nat := 118140960795 + 5168637 * 2 ^ 59
def prefixEnd_5168637 : Nat := 4983230072969 + 3 ^ 40 * 5168637 * 2
def baseEnd_5168637 : Nat := 2653995109612799417667377

theorem tailTrace_5168637 : CollatzResearch.WordTrace tailWord_5168637 prefixEnd_5168637 2653995109612799417667377 := by
  unfold tailWord_5168637
  simp only [CollatzResearch.WordTrace]
  refine ⟨188515678575918356766752165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125677119050612237844501443 188515678575918356766752165)
  ·
    refine ⟨35346689732984691893766031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188515678575918356766752165 35346689732984691893766031)
    ·
      refine ⟨53020034599477037840649047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35346689732984691893766031 53020034599477037840649047)
      ·
        refine ⟨79530051899215556760973571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53020034599477037840649047 79530051899215556760973571)
        ·
          refine ⟨119295077848823335141460357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79530051899215556760973571 119295077848823335141460357)
          ·
            refine ⟨22367827096654375339023817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119295077848823335141460357 22367827096654375339023817)
            ·
              refine ⟨16775870322490781504267863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22367827096654375339023817 16775870322490781504267863)
              ·
                refine ⟨25163805483736172256401795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16775870322490781504267863 25163805483736172256401795)
                ·
                  refine ⟨37745708225604258384602693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25163805483736172256401795 37745708225604258384602693)
                  ·
                    refine ⟨7077320292300798447113005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37745708225604258384602693 7077320292300798447113005)
                    ·
                      refine ⟨2653995109612799417667377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7077320292300798447113005 2653995109612799417667377)
                      ·
                        rfl

theorem cell23_5168637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_5168637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168637 prefixEnd_5168637 := by exact prefixLift 5168637
  have htrace : WordTrace (prefixWord ++ tailWord_5168637) baseStart_5168637 baseEnd_5168637 := by
    simpa [prefixWord, tailWord_5168637, baseEnd_5168637] using wordTrace_append hprefix tailTrace_5168637
  have hstable : (prefixWord ++ tailWord_5168637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168637).length < 2 ^ (prefixWord ++ tailWord_5168637).sum := by decide
  have hdescent : baseEnd_5168637 < baseStart_5168637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168674 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_5168674 : Nat := 118140960795 + 5168674 * 2 ^ 59
def prefixEnd_5168674 : Nat := 4983230072969 + 3 ^ 40 * 5168674 * 2
def baseEnd_5168674 : Nat := 294890456488557308100523

theorem tailTrace_5168674 : CollatzResearch.WordTrace tailWord_5168674 prefixEnd_5168674 294890456488557308100523 := by
  unfold tailWord_5168674
  simp only [CollatzResearch.WordTrace]
  refine ⟨47129257019196078021462269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125678018717856208057232717 47129257019196078021462269)
  ·
    refine ⟨17673471382198529258048351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47129257019196078021462269 17673471382198529258048351)
    ·
      refine ⟨26510207073297793887072527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17673471382198529258048351 26510207073297793887072527)
      ·
        refine ⟨39765310609946690830608791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26510207073297793887072527 39765310609946690830608791)
        ·
          refine ⟨59647965914920036245913187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39765310609946690830608791 59647965914920036245913187)
          ·
            refine ⟨89471948872380054368869781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59647965914920036245913187 89471948872380054368869781)
            ·
              refine ⟨4193997603392815048540771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89471948872380054368869781 4193997603392815048540771)
              ·
                refine ⟨6290996405089222572811157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193997603392815048540771 6290996405089222572811157)
                ·
                  refine ⟨294890456488557308100523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6290996405089222572811157 294890456488557308100523)
                  ·
                    rfl

theorem cell23_5168674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_5168674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168674 prefixEnd_5168674 := by exact prefixLift 5168674
  have htrace : WordTrace (prefixWord ++ tailWord_5168674) baseStart_5168674 baseEnd_5168674 := by
    simpa [prefixWord, tailWord_5168674, baseEnd_5168674] using wordTrace_append hprefix tailTrace_5168674
  have hstable : (prefixWord ++ tailWord_5168674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168674).length < 2 ^ (prefixWord ++ tailWord_5168674).sum := by decide
  have hdescent : baseEnd_5168674 < baseStart_5168674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168741 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_5168741 : Nat := 118140960795 + 5168741 * 2 ^ 59
def prefixEnd_5168741 : Nat := 4983230072969 + 3 ^ 40 * 5168741 * 2
def baseEnd_5168741 : Nat := 2654048511600867010766899

theorem tailTrace_5168741 : CollatzResearch.WordTrace tailWord_5168741 prefixEnd_5168741 2654048511600867010766899 := by
  unfold tailWord_5168741
  simp only [CollatzResearch.WordTrace]
  refine ⟨188519471767541582528538077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125679647845027721685692051 188519471767541582528538077)
  ·
    refine ⟨70694801912828093448201779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188519471767541582528538077 70694801912828093448201779)
    ·
      refine ⟨106042202869242140172302669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70694801912828093448201779 106042202869242140172302669)
      ·
        refine ⟨39765826075965802564613501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106042202869242140172302669 39765826075965802564613501)
        ·
          refine ⟨14912184778487175961730063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39765826075965802564613501 14912184778487175961730063)
          ·
            refine ⟨22368277167730763942595095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912184778487175961730063 22368277167730763942595095)
            ·
              refine ⟨33552415751596145913892643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22368277167730763942595095 33552415751596145913892643)
              ·
                refine ⟨50328623627394218870838965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33552415751596145913892643 50328623627394218870838965)
                ·
                  refine ⟨4718308465068208019141153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50328623627394218870838965 4718308465068208019141153)
                  ·
                    refine ⟨3538731348801156014355865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718308465068208019141153 3538731348801156014355865)
                    ·
                      refine ⟨2654048511600867010766899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538731348801156014355865 2654048511600867010766899)
                      ·
                        rfl

theorem cell23_5168741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_5168741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168741 prefixEnd_5168741 := by exact prefixLift 5168741
  have htrace : WordTrace (prefixWord ++ tailWord_5168741) baseStart_5168741 baseEnd_5168741 := by
    simpa [prefixWord, tailWord_5168741, baseEnd_5168741] using wordTrace_append hprefix tailTrace_5168741
  have hstable : (prefixWord ++ tailWord_5168741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168741).length < 2 ^ (prefixWord ++ tailWord_5168741).sum := by decide
  have hdescent : baseEnd_5168741 < baseStart_5168741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168754 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5168754 : Nat := 118140960795 + 5168754 * 2 ^ 59
def prefixEnd_5168754 : Nat := 4983230072969 + 3 ^ 40 * 5168754 * 2
def baseEnd_5168754 : Nat := 2654055186849375459904339

theorem tailTrace_5168754 : CollatzResearch.WordTrace tailWord_5168754 prefixEnd_5168754 2654055186849375459904339 := by
  unfold tailWord_5168754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47129986479123621437190329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125679963944329657165840877 47129986479123621437190329)
  ·
    refine ⟨35347489859342716077892747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47129986479123621437190329 35347489859342716077892747)
    ·
      refine ⟨53021234789014074116839121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35347489859342716077892747 53021234789014074116839121)
      ·
        refine ⟨39765926091760555587629341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53021234789014074116839121 39765926091760555587629341)
        ·
          refine ⟨14912222284410208345361003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39765926091760555587629341 14912222284410208345361003)
          ·
            refine ⟨22368333426615312518041505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912222284410208345361003 22368333426615312518041505)
            ·
              refine ⟨16776250069961484388531129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22368333426615312518041505 16776250069961484388531129)
              ·
                refine ⟨12582187552471113291398347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16776250069961484388531129 12582187552471113291398347)
                ·
                  refine ⟨18873281328706669937097521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12582187552471113291398347 18873281328706669937097521)
                  ·
                    refine ⟨14154960996530002452823141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18873281328706669937097521 14154960996530002452823141)
                    ·
                      refine ⟨2654055186849375459904339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14154960996530002452823141 2654055186849375459904339)
                      ·
                        rfl

theorem cell23_5168754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5168754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168754 prefixEnd_5168754 := by exact prefixLift 5168754
  have htrace : WordTrace (prefixWord ++ tailWord_5168754) baseStart_5168754 baseEnd_5168754 := by
    simpa [prefixWord, tailWord_5168754, baseEnd_5168754] using wordTrace_append hprefix tailTrace_5168754
  have hstable : (prefixWord ++ tailWord_5168754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168754).length < 2 ^ (prefixWord ++ tailWord_5168754).sum := by decide
  have hdescent : baseEnd_5168754 < baseStart_5168754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168758 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5168758 : Nat := 118140960795 + 5168758 * 2 ^ 59
def prefixEnd_5168758 : Nat := 4983230072969 + 3 ^ 40 * 5168758 * 2
def baseEnd_5168758 : Nat := 2654057240771993444254321

theorem tailTrace_5168758 : CollatzResearch.WordTrace tailWord_5168758 prefixEnd_5168758 2654057240771993444254321 := by
  unfold tailWord_5168758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782505738029999651994183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125680061205653329621271285 11782505738029999651994183)
  ·
    refine ⟨17673758607044999477991275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11782505738029999651994183 17673758607044999477991275)
    ·
      refine ⟨26510637910567499216986913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17673758607044999477991275 26510637910567499216986913)
      ·
        refine ⟨19882978432925624412740185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26510637910567499216986913 19882978432925624412740185)
        ·
          refine ⟨14912233824694218309555139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19882978432925624412740185 14912233824694218309555139)
          ·
            refine ⟨22368350737041327464332709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912233824694218309555139 22368350737041327464332709)
            ·
              refine ⟨4194065763195248899562383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22368350737041327464332709 4194065763195248899562383)
              ·
                refine ⟨6291098644792873349343575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194065763195248899562383 6291098644792873349343575)
                ·
                  refine ⟨9436647967189310024015363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291098644792873349343575 9436647967189310024015363)
                  ·
                    refine ⟨14154971950783965036023045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9436647967189310024015363 14154971950783965036023045)
                    ·
                      refine ⟨2654057240771993444254321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14154971950783965036023045 2654057240771993444254321)
                      ·
                        rfl

theorem cell23_5168758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5168758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168758 prefixEnd_5168758 := by exact prefixLift 5168758
  have htrace : WordTrace (prefixWord ++ tailWord_5168758) baseStart_5168758 baseEnd_5168758 := by
    simpa [prefixWord, tailWord_5168758, baseEnd_5168758] using wordTrace_append hprefix tailTrace_5168758
  have hstable : (prefixWord ++ tailWord_5168758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168758).length < 2 ^ (prefixWord ++ tailWord_5168758).sum := by decide
  have hdescent : baseEnd_5168758 < baseStart_5168758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168784 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2]
def baseStart_5168784 : Nat := 118140960795 + 5168784 * 2 ^ 59
def prefixEnd_5168784 : Nat := 4983230072969 + 3 ^ 40 * 5168784 * 2
def baseEnd_5168784 : Nat := 2654070591269010342529201

theorem tailTrace_5168784 : CollatzResearch.WordTrace tailWord_5168784 prefixEnd_5168784 2654070591269010342529201 := by
  unfold tailWord_5168784
  simp only [CollatzResearch.WordTrace]
  refine ⟨94260520053192900436176703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125680693404257200581568937 94260520053192900436176703)
  ·
    refine ⟨141390780079789350654265055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94260520053192900436176703 141390780079789350654265055)
    ·
      refine ⟨212086170119684025981397583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141390780079789350654265055 212086170119684025981397583)
      ·
        refine ⟨318129255179526038972096375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212086170119684025981397583 318129255179526038972096375)
        ·
          refine ⟨477193882769289058458144563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318129255179526038972096375 477193882769289058458144563)
          ·
            refine ⟨715790824153933587687216845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477193882769289058458144563 715790824153933587687216845)
            ·
              refine ⟨268421559057725095382706317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715790824153933587687216845 268421559057725095382706317)
              ·
                refine ⟨100658084646646910768514869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268421559057725095382706317 100658084646646910768514869)
                ·
                  refine ⟨9436695435623147884548269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100658084646646910768514869 9436695435623147884548269)
                  ·
                    refine ⟨3538760788358680456705601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9436695435623147884548269 3538760788358680456705601)
                    ·
                      refine ⟨2654070591269010342529201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538760788358680456705601 2654070591269010342529201)
                      ·
                        rfl

theorem cell23_5168784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2].length) (baseStart_5168784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168784 prefixEnd_5168784 := by exact prefixLift 5168784
  have htrace : WordTrace (prefixWord ++ tailWord_5168784) baseStart_5168784 baseEnd_5168784 := by
    simpa [prefixWord, tailWord_5168784, baseEnd_5168784] using wordTrace_append hprefix tailTrace_5168784
  have hstable : (prefixWord ++ tailWord_5168784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168784).length < 2 ^ (prefixWord ++ tailWord_5168784).sum := by decide
  have hdescent : baseEnd_5168784 < baseStart_5168784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168788 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_5168788 : Nat := 118140960795 + 5168788 * 2 ^ 59
def prefixEnd_5168788 : Nat := 4983230072969 + 3 ^ 40 * 5168788 * 2
def baseEnd_5168788 : Nat := 2654072645191628326879183

theorem tailTrace_5168788 : CollatzResearch.WordTrace tailWord_5168788 prefixEnd_5168788 2654072645191628326879183 := by
  unfold tailWord_5168788
  simp only [CollatzResearch.WordTrace]
  refine ⟨94260592999185654777749509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125680790665580873036999345 94260592999185654777749509)
  ·
    refine ⟨17673861187347310270828033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94260592999185654777749509 17673861187347310270828033)
    ·
      refine ⟨13255395890510482703121025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17673861187347310270828033 13255395890510482703121025)
      ·
        refine ⟨9941546917882862027340769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13255395890510482703121025 9941546917882862027340769)
        ·
          refine ⟨7456160188412146520505577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9941546917882862027340769 7456160188412146520505577)
          ·
            refine ⟨5592120141309109890379183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7456160188412146520505577 5592120141309109890379183)
            ·
              refine ⟨8388180211963664835568775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592120141309109890379183 8388180211963664835568775)
              ·
                refine ⟨12582270317945497253353163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8388180211963664835568775 12582270317945497253353163)
                ·
                  refine ⟨18873405476918245880029745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12582270317945497253353163 18873405476918245880029745)
                  ·
                    refine ⟨14155054107688684410022309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18873405476918245880029745 14155054107688684410022309)
                    ·
                      refine ⟨2654072645191628326879183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14155054107688684410022309 2654072645191628326879183)
                      ·
                        rfl

theorem cell23_5168788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_5168788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168788 prefixEnd_5168788 := by exact prefixLift 5168788
  have htrace : WordTrace (prefixWord ++ tailWord_5168788) baseStart_5168788 baseEnd_5168788 := by
    simpa [prefixWord, tailWord_5168788, baseEnd_5168788] using wordTrace_append hprefix tailTrace_5168788
  have hstable : (prefixWord ++ tailWord_5168788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168788).length < 2 ^ (prefixWord ++ tailWord_5168788).sum := by decide
  have hdescent : baseEnd_5168788 < baseStart_5168788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168791 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_5168791 : Nat := 118140960795 + 5168791 * 2 ^ 59
def prefixEnd_5168791 : Nat := 4983230072969 + 3 ^ 40 * 5168791 * 2
def baseEnd_5168791 : Nat := 2654074185633591815141669

theorem tailTrace_5168791 : CollatzResearch.WordTrace tailWord_5168791 prefixEnd_5168791 2654074185633591815141669 := by
  unfold tailWord_5168791
  simp only [CollatzResearch.WordTrace]
  refine ⟨188521295417360441067858227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125680863611573627378572151 188521295417360441067858227)
  ·
    refine ⟨282781943126040661601787341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188521295417360441067858227 282781943126040661601787341)
    ·
      refine ⟨106043228672265248100670253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282781943126040661601787341 106043228672265248100670253)
      ·
        refine ⟨39766210752099468037751345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106043228672265248100670253 39766210752099468037751345)
        ·
          refine ⟨29824658064074601028313509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39766210752099468037751345 29824658064074601028313509)
          ·
            refine ⟨5592123387013987692808783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29824658064074601028313509 5592123387013987692808783)
            ·
              refine ⟨8388185080520981539213175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592123387013987692808783 8388185080520981539213175)
              ·
                refine ⟨12582277620781472308819763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8388185080520981539213175 12582277620781472308819763)
                ·
                  refine ⟨18873416431172208463229645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12582277620781472308819763 18873416431172208463229645)
                  ·
                    refine ⟨7077531161689578173711117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18873416431172208463229645 7077531161689578173711117)
                    ·
                      refine ⟨2654074185633591815141669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7077531161689578173711117 2654074185633591815141669)
                      ·
                        rfl

theorem cell23_5168791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_5168791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168791 prefixEnd_5168791 := by exact prefixLift 5168791
  have htrace : WordTrace (prefixWord ++ tailWord_5168791) baseStart_5168791 baseEnd_5168791 := by
    simpa [prefixWord, tailWord_5168791, baseEnd_5168791] using wordTrace_append hprefix tailTrace_5168791
  have hstable : (prefixWord ++ tailWord_5168791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168791).length < 2 ^ (prefixWord ++ tailWord_5168791).sum := by decide
  have hdescent : baseEnd_5168791 < baseStart_5168791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168827 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_5168827 : Nat := 118140960795 + 5168827 * 2 ^ 59
def prefixEnd_5168827 : Nat := 4983230072969 + 3 ^ 40 * 5168827 * 2
def baseEnd_5168827 : Nat := 2654092670937153674291503

theorem tailTrace_5168827 : CollatzResearch.WordTrace tailWord_5168827 prefixEnd_5168827 2654092670937153674291503 := by
  unfold tailWord_5168827
  simp only [CollatzResearch.WordTrace]
  refine ⟨188522608445230019216168735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125681738963486679477445823 188522608445230019216168735)
  ·
    refine ⟨282783912667845028824253103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188522608445230019216168735 282783912667845028824253103)
    ·
      refine ⟨424175869001767543236379655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282783912667845028824253103 424175869001767543236379655)
      ·
        refine ⟨636263803502651314854569483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424175869001767543236379655 636263803502651314854569483)
        ·
          refine ⟨954395705253976972281854225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636263803502651314854569483 954395705253976972281854225)
          ·
            refine ⟨715796778940482729211390669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954395705253976972281854225 715796778940482729211390669)
            ·
              refine ⟨268423792102681023454271501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715796778940482729211390669 268423792102681023454271501)
              ·
                refine ⟨100658922038505383795351813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268423792102681023454271501 100658922038505383795351813)
                ·
                  refine ⟨18873547882219759461628465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100658922038505383795351813 18873547882219759461628465)
                  ·
                    refine ⟨14155160911664819596221349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18873547882219759461628465 14155160911664819596221349)
                    ·
                      refine ⟨2654092670937153674291503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14155160911664819596221349 2654092670937153674291503)
                      ·
                        rfl

theorem cell23_5168827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_5168827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168827 prefixEnd_5168827 := by exact prefixLift 5168827
  have htrace : WordTrace (prefixWord ++ tailWord_5168827) baseStart_5168827 baseEnd_5168827 := by
    simpa [prefixWord, tailWord_5168827, baseEnd_5168827] using wordTrace_append hprefix tailTrace_5168827
  have hstable : (prefixWord ++ tailWord_5168827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168827).length < 2 ^ (prefixWord ++ tailWord_5168827).sum := by decide
  have hdescent : baseEnd_5168827 < baseStart_5168827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168831 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 4, 2, 2]
def baseStart_5168831 : Nat := 118140960795 + 5168831 * 2 ^ 59
def prefixEnd_5168831 : Nat := 4983230072969 + 3 ^ 40 * 5168831 * 2
def baseEnd_5168831 : Nat := 2654094724859771658641485

theorem tailTrace_5168831 : CollatzResearch.WordTrace tailWord_5168831 prefixEnd_5168831 2654094724859771658641485 := by
  unfold tailWord_5168831
  simp only [CollatzResearch.WordTrace]
  refine ⟨188522754337215527899314347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125681836224810351932876231 188522754337215527899314347)
  ·
    refine ⟨282784131505823291848971521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188522754337215527899314347 282784131505823291848971521)
    ·
      refine ⟨212088098629367468886728641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282784131505823291848971521 212088098629367468886728641)
      ·
        refine ⟨159066073972025601665046481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212088098629367468886728641 159066073972025601665046481)
        ·
          refine ⟨119299555479019201248784861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159066073972025601665046481 119299555479019201248784861)
          ·
            refine ⟨44737333304632200468294323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119299555479019201248784861 44737333304632200468294323)
            ·
              refine ⟨67105999956948300702441485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44737333304632200468294323 67105999956948300702441485)
              ·
                refine ⟨25164749983855612763415557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67105999956948300702441485 25164749983855612763415557)
                ·
                  refine ⟨4718390621972927393140417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25164749983855612763415557 4718390621972927393140417)
                  ·
                    refine ⟨3538792966479695544855313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718390621972927393140417 3538792966479695544855313)
                    ·
                      refine ⟨2654094724859771658641485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538792966479695544855313 2654094724859771658641485)
                      ·
                        rfl

theorem cell23_5168831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_5168831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168831 prefixEnd_5168831 := by exact prefixLift 5168831
  have htrace : WordTrace (prefixWord ++ tailWord_5168831) baseStart_5168831 baseEnd_5168831 := by
    simpa [prefixWord, tailWord_5168831, baseEnd_5168831] using wordTrace_append hprefix tailTrace_5168831
  have hstable : (prefixWord ++ tailWord_5168831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168831).length < 2 ^ (prefixWord ++ tailWord_5168831).sum := by decide
  have hdescent : baseEnd_5168831 < baseStart_5168831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168842 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_5168842 : Nat := 118140960795 + 5168842 * 2 ^ 59
def prefixEnd_5168842 : Nat := 4983230072969 + 3 ^ 40 * 5168842 * 2
def baseEnd_5168842 : Nat := 2654100373146971115603935

theorem tailTrace_5168842 : CollatzResearch.WordTrace tailWord_5168842 prefixEnd_5168842 2654100373146971115603935 := by
  unfold tailWord_5168842
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130788885043919194491195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125682103693450451185309853 47130788885043919194491195)
  ·
    refine ⟨70696183327565878791736793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47130788885043919194491195 70696183327565878791736793)
    ·
      refine ⟨53022137495674409093802595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70696183327565878791736793 53022137495674409093802595)
      ·
        refine ⟨79533206243511613640703893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53022137495674409093802595 79533206243511613640703893)
        ·
          refine ⟨3728119042664606889407995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79533206243511613640703893 3728119042664606889407995)
          ·
            refine ⟨5592178563996910334111993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728119042664606889407995 5592178563996910334111993)
            ·
              refine ⟨4194133922997682750583995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5592178563996910334111993 4194133922997682750583995)
              ·
                refine ⟨6291200884496524125875993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194133922997682750583995 6291200884496524125875993)
                ·
                  refine ⟨4718400663372393094406995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291200884496524125875993 4718400663372393094406995)
                  ·
                    refine ⟨7077600995058589641610493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4718400663372393094406995 7077600995058589641610493)
                    ·
                      refine ⟨2654100373146971115603935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7077600995058589641610493 2654100373146971115603935)
                      ·
                        rfl

theorem cell23_5168842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_5168842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168842 prefixEnd_5168842 := by exact prefixLift 5168842
  have htrace : WordTrace (prefixWord ++ tailWord_5168842) baseStart_5168842 baseEnd_5168842 := by
    simpa [prefixWord, tailWord_5168842, baseEnd_5168842] using wordTrace_append hprefix tailTrace_5168842
  have hstable : (prefixWord ++ tailWord_5168842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168842).length < 2 ^ (prefixWord ++ tailWord_5168842).sum := by decide
  have hdescent : baseEnd_5168842 < baseStart_5168842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168904 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_5168904 : Nat := 118140960795 + 5168904 * 2 ^ 59
def prefixEnd_5168904 : Nat := 4983230072969 + 3 ^ 40 * 5168904 * 2
def baseEnd_5168904 : Nat := 2654132208947549873028649

theorem tailTrace_5168904 : CollatzResearch.WordTrace tailWord_5168904 prefixEnd_5168904 2654132208947549873028649 := by
  unfold tailWord_5168904
  simp only [CollatzResearch.WordTrace]
  refine ⟨94262708432975530683360883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125683611243967374244481177 94262708432975530683360883)
  ·
    refine ⟨141394062649463296025041325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94262708432975530683360883 141394062649463296025041325)
    ·
      refine ⟨53022773493548736009390497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141394062649463296025041325 53022773493548736009390497)
      ·
        refine ⟨39767080120161552007042873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53022773493548736009390497 39767080120161552007042873)
        ·
          refine ⟨29825310090121164005282155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39767080120161552007042873 29825310090121164005282155)
          ·
            refine ⟨44737965135181746007923233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29825310090121164005282155 44737965135181746007923233)
            ·
              refine ⟨33553473851386309505942425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44737965135181746007923233 33553473851386309505942425)
              ·
                refine ⟨25165105388539732129456819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33553473851386309505942425 25165105388539732129456819)
                ·
                  refine ⟨37747658082809598194185229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25165105388539732129456819 37747658082809598194185229)
                  ·
                    refine ⟨14155371781053599322819461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37747658082809598194185229 14155371781053599322819461)
                    ·
                      refine ⟨2654132208947549873028649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14155371781053599322819461 2654132208947549873028649)
                      ·
                        rfl

theorem cell23_5168904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_5168904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168904 prefixEnd_5168904 := by exact prefixLift 5168904
  have htrace : WordTrace (prefixWord ++ tailWord_5168904) baseStart_5168904 baseEnd_5168904 := by
    simpa [prefixWord, tailWord_5168904, baseEnd_5168904] using wordTrace_append hprefix tailTrace_5168904
  have hstable : (prefixWord ++ tailWord_5168904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168904).length < 2 ^ (prefixWord ++ tailWord_5168904).sum := by decide
  have hdescent : baseEnd_5168904 < baseStart_5168904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168948 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5168948 : Nat := 118140960795 + 5168948 * 2 ^ 59
def prefixEnd_5168948 : Nat := 4983230072969 + 3 ^ 40 * 5168948 * 2
def baseEnd_5168948 : Nat := 884718267365449233626149

theorem tailTrace_5168948 : CollatzResearch.WordTrace tailWord_5168948 prefixEnd_5168948 884718267365449233626149 := by
  unfold tailWord_5168948
  simp only [CollatzResearch.WordTrace]
  refine ⟨94263510838895828440661749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125684681118527771254215665 94263510838895828440661749)
  ·
    refine ⟨8837204141146483916312039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94263510838895828440661749 8837204141146483916312039)
    ·
      refine ⟨13255806211719725874468059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837204141146483916312039 13255806211719725874468059)
      ·
        refine ⟨19883709317579588811702089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13255806211719725874468059 19883709317579588811702089)
        ·
          refine ⟨14912781988184691608776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19883709317579588811702089 14912781988184691608776567)
          ·
            refine ⟨22369172982277037413164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14912781988184691608776567 22369172982277037413164851)
            ·
              refine ⟨33553759473415556119747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22369172982277037413164851 33553759473415556119747277)
              ·
                refine ⟨12582659802530833544905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33553759473415556119747277 12582659802530833544905229)
                ·
                  refine ⟨4718497425949062579339461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12582659802530833544905229 4718497425949062579339461)
                  ·
                    refine ⟨884718267365449233626149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718497425949062579339461 884718267365449233626149)
                    ·
                      rfl

theorem cell23_5168948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5168948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168948 prefixEnd_5168948 := by exact prefixLift 5168948
  have htrace : WordTrace (prefixWord ++ tailWord_5168948) baseStart_5168948 baseEnd_5168948 := by
    simpa [prefixWord, tailWord_5168948, baseEnd_5168948] using wordTrace_append hprefix tailTrace_5168948
  have hstable : (prefixWord ++ tailWord_5168948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168948).length < 2 ^ (prefixWord ++ tailWord_5168948).sum := by decide
  have hdescent : baseEnd_5168948 < baseStart_5168948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5168991 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 1, 5]
def baseStart_5168991 : Nat := 118140960795 + 5168991 * 2 ^ 59
def prefixEnd_5168991 : Nat := 4983230072969 + 3 ^ 40 * 5168991 * 2
def baseEnd_5168991 : Nat := 884725627254830344213583

theorem tailTrace_5168991 : CollatzResearch.WordTrace tailWord_5168991 prefixEnd_5168991 884725627254830344213583 := by
  unfold tailWord_5168991
  simp only [CollatzResearch.WordTrace]
  refine ⟨188528590016635875225138827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125685726677757250150092551 188528590016635875225138827)
  ·
    refine ⟨282792885024953812837708241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188528590016635875225138827 282792885024953812837708241)
    ·
      refine ⟨212094663768715359628281181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282792885024953812837708241 212094663768715359628281181)
      ·
        refine ⟨79535498913268259860605443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212094663768715359628281181 79535498913268259860605443)
        ·
          refine ⟨119303248369902389790908165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79535498913268259860605443 119303248369902389790908165)
          ·
            refine ⟨22369359069356698085795281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119303248369902389790908165 22369359069356698085795281)
            ·
              refine ⟨16777019302017523564346461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22369359069356698085795281 16777019302017523564346461)
              ·
                refine ⟨6291382238256571336629923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16777019302017523564346461 6291382238256571336629923)
                ·
                  refine ⟨9437073357384857004944885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291382238256571336629923 9437073357384857004944885)
                  ·
                    refine ⟨884725627254830344213583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9437073357384857004944885 884725627254830344213583)
                    ·
                      rfl

theorem cell23_5168991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_5168991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5168991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5168991 prefixEnd_5168991 := by exact prefixLift 5168991
  have htrace : WordTrace (prefixWord ++ tailWord_5168991) baseStart_5168991 baseEnd_5168991 := by
    simpa [prefixWord, tailWord_5168991, baseEnd_5168991] using wordTrace_append hprefix tailTrace_5168991
  have hstable : (prefixWord ++ tailWord_5168991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5168991).length < 2 ^ (prefixWord ++ tailWord_5168991).sum := by decide
  have hdescent : baseEnd_5168991 < baseStart_5168991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5168991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169005 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5169005 : Nat := 118140960795 + 5169005 * 2 ^ 59
def prefixEnd_5169005 : Nat := 4983230072969 + 3 ^ 40 * 5169005 * 2
def baseEnd_5169005 : Nat := 2654184070493653977865685

theorem tailTrace_5169005 : CollatzResearch.WordTrace tailWord_5169005 prefixEnd_5169005 2654184070493653977865685 := by
  unfold tailWord_5169005
  simp only [CollatzResearch.WordTrace]
  refine ⟨188529100638585155616148469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125686067092390103744098979 188529100638585155616148469)
  ·
    refine ⟨17674603184867358339013919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188529100638585155616148469 17674603184867358339013919)
    ·
      refine ⟨26511904777301037508520879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17674603184867358339013919 26511904777301037508520879)
      ·
        refine ⟨39767857165951556262781319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26511904777301037508520879 39767857165951556262781319)
        ·
          refine ⟨59651785748927334394171979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39767857165951556262781319 59651785748927334394171979)
          ·
            refine ⟨89477678623391001591257969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59651785748927334394171979 89477678623391001591257969)
            ·
              refine ⟨67108258967543251193443477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89477678623391001591257969 67108258967543251193443477)
              ·
                refine ⟨3145699639103589899692663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67108258967543251193443477 3145699639103589899692663)
                ·
                  refine ⟨4718549458655384849538995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145699639103589899692663 4718549458655384849538995)
                  ·
                    refine ⟨7077824187983077274308493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4718549458655384849538995 7077824187983077274308493)
                    ·
                      refine ⟨2654184070493653977865685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7077824187983077274308493 2654184070493653977865685)
                      ·
                        rfl

theorem cell23_5169005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5169005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169005 prefixEnd_5169005 := by exact prefixLift 5169005
  have htrace : WordTrace (prefixWord ++ tailWord_5169005) baseStart_5169005 baseEnd_5169005 := by
    simpa [prefixWord, tailWord_5169005, baseEnd_5169005] using wordTrace_append hprefix tailTrace_5169005
  have hstable : (prefixWord ++ tailWord_5169005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169005).length < 2 ^ (prefixWord ++ tailWord_5169005).sum := by decide
  have hdescent : baseEnd_5169005 < baseStart_5169005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169024 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_5169024 : Nat := 118140960795 + 5169024 * 2 ^ 59
def prefixEnd_5169024 : Nat := 4983230072969 + 3 ^ 40 * 5169024 * 2
def baseEnd_5169024 : Nat := 2654193826626089403528097

theorem tailTrace_5169024 : CollatzResearch.WordTrace tailWord_5169024 prefixEnd_5169024 2654193826626089403528097 := by
  unfold tailWord_5169024
  simp only [CollatzResearch.WordTrace]
  refine ⟨94264896812758160930545063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125686529083677547907393417 94264896812758160930545063)
  ·
    refine ⟨141397345219137241395817595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94264896812758160930545063 141397345219137241395817595)
    ·
      refine ⟨212096017828705862093726393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141397345219137241395817595 212096017828705862093726393)
      ·
        refine ⟨159072013371529396570294795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212096017828705862093726393 159072013371529396570294795)
        ·
          refine ⟨238608020057294094855442193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159072013371529396570294795 238608020057294094855442193)
          ·
            refine ⟨178956015042970571141581645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238608020057294094855442193 178956015042970571141581645)
            ·
              refine ⟨67108505641113964178093117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178956015042970571141581645 67108505641113964178093117)
              ·
                refine ⟨25165689615417736566784919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67108505641113964178093117 25165689615417736566784919)
                ·
                  refine ⟨37748534423126604850177379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25165689615417736566784919 37748534423126604850177379)
                  ·
                    refine ⟨56622801634689907275266069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37748534423126604850177379 56622801634689907275266069)
                    ·
                      refine ⟨2654193826626089403528097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56622801634689907275266069 2654193826626089403528097)
                      ·
                        rfl

theorem cell23_5169024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_5169024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169024 prefixEnd_5169024 := by exact prefixLift 5169024
  have htrace : WordTrace (prefixWord ++ tailWord_5169024) baseStart_5169024 baseEnd_5169024 := by
    simpa [prefixWord, tailWord_5169024, baseEnd_5169024] using wordTrace_append hprefix tailTrace_5169024
  have hstable : (prefixWord ++ tailWord_5169024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169024).length < 2 ^ (prefixWord ++ tailWord_5169024).sum := by decide
  have hdescent : baseEnd_5169024 < baseStart_5169024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169028 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_5169028 : Nat := 118140960795 + 5169028 * 2 ^ 59
def prefixEnd_5169028 : Nat := 4983230072969 + 3 ^ 40 * 5169028 * 2
def baseEnd_5169028 : Nat := 2654195880548707387878079

theorem tailTrace_5169028 : CollatzResearch.WordTrace tailWord_5169028 prefixEnd_5169028 2654195880548707387878079 := by
  unfold tailWord_5169028
  simp only [CollatzResearch.WordTrace]
  refine ⟨94264969758750915272117869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125686626345001220362823825 94264969758750915272117869)
  ·
    refine ⟨35349363659531593227044201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94264969758750915272117869 35349363659531593227044201)
    ·
      refine ⟨26512022744648694920283151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35349363659531593227044201 26512022744648694920283151)
      ·
        refine ⟨39768034116973042380424727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26512022744648694920283151 39768034116973042380424727)
        ·
          refine ⟨59652051175459563570637091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39768034116973042380424727 59652051175459563570637091)
          ·
            refine ⟨89478076763189345355955637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59652051175459563570637091 89478076763189345355955637)
            ·
              refine ⟨8388569696549001127120841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89478076763189345355955637 8388569696549001127120841)
              ·
                refine ⟨6291427272411750845340631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8388569696549001127120841 6291427272411750845340631)
                ·
                  refine ⟨9437140908617626268010947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291427272411750845340631 9437140908617626268010947)
                  ·
                    refine ⟨14155711362926439402016421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9437140908617626268010947 14155711362926439402016421)
                    ·
                      refine ⟨2654195880548707387878079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14155711362926439402016421 2654195880548707387878079)
                      ·
                        rfl

theorem cell23_5169028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_5169028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169028 prefixEnd_5169028 := by exact prefixLift 5169028
  have htrace : WordTrace (prefixWord ++ tailWord_5169028) baseStart_5169028 baseEnd_5169028 := by
    simpa [prefixWord, tailWord_5169028, baseEnd_5169028] using wordTrace_append hprefix tailTrace_5169028
  have hstable : (prefixWord ++ tailWord_5169028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169028).length < 2 ^ (prefixWord ++ tailWord_5169028).sum := by decide
  have hdescent : baseEnd_5169028 < baseStart_5169028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169055 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 2, 4]
def baseStart_5169055 : Nat := 118140960795 + 5169055 * 2 ^ 59
def prefixEnd_5169055 : Nat := 4983230072969 + 3 ^ 40 * 5169055 * 2
def baseEnd_5169055 : Nat := 884736581508792927413485

theorem tailTrace_5169055 : CollatzResearch.WordTrace tailWord_5169055 prefixEnd_5169055 884736581508792927413485 := by
  unfold tailWord_5169055
  simp only [CollatzResearch.WordTrace]
  refine ⟨188530924288404014155468619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125687282858936009436979079 188530924288404014155468619)
  ·
    refine ⟨282796386432606021233202929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188530924288404014155468619 282796386432606021233202929)
    ·
      refine ⟨212097289824454515924902197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282796386432606021233202929 212097289824454515924902197)
      ·
        refine ⟨19884120921042610867959581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212097289824454515924902197 19884120921042610867959581)
        ·
          refine ⟨7456545345390979075484843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19884120921042610867959581 7456545345390979075484843)
          ·
            refine ⟨11184818018086468613227265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7456545345390979075484843 11184818018086468613227265)
            ·
              refine ⟨8388613513564851459920449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11184818018086468613227265 8388613513564851459920449)
              ·
                refine ⟨6291460135173638594940337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8388613513564851459920449 6291460135173638594940337)
                ·
                  refine ⟨4718595101380228946205253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6291460135173638594940337 4718595101380228946205253)
                  ·
                    refine ⟨884736581508792927413485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718595101380228946205253 884736581508792927413485)
                    ·
                      rfl

theorem cell23_5169055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_5169055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169055 prefixEnd_5169055 := by exact prefixLift 5169055
  have htrace : WordTrace (prefixWord ++ tailWord_5169055) baseStart_5169055 baseEnd_5169055 := by
    simpa [prefixWord, tailWord_5169055, baseEnd_5169055] using wordTrace_append hprefix tailTrace_5169055
  have hstable : (prefixWord ++ tailWord_5169055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169055).length < 2 ^ (prefixWord ++ tailWord_5169055).sum := by decide
  have hdescent : baseEnd_5169055 < baseStart_5169055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169088 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2]
def baseStart_5169088 : Nat := 118140960795 + 5169088 * 2 ^ 59
def prefixEnd_5169088 : Nat := 4983230072969 + 3 ^ 40 * 5169088 * 2
def baseEnd_5169088 : Nat := 2654226689387977153127803

theorem tailTrace_5169088 : CollatzResearch.WordTrace tailWord_5169088 prefixEnd_5169088 2654226689387977153127803 := by
  unfold tailWord_5169088
  simp only [CollatzResearch.WordTrace]
  refine ⟨94266063948642230395709959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125688085264856307194279945 94266063948642230395709959)
  ·
    refine ⟨141399095922963345593564939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94266063948642230395709959 141399095922963345593564939)
    ·
      refine ⟨212098643884445018390347409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141399095922963345593564939 212098643884445018390347409)
      ·
        refine ⟨159073982913333763792760557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212098643884445018390347409 159073982913333763792760557)
        ·
          refine ⟨59652743592500161422285209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159073982913333763792760557 59652743592500161422285209)
          ·
            refine ⟨44739557694375121066713907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59652743592500161422285209 44739557694375121066713907)
            ·
              refine ⟨67109336541562681600070861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44739557694375121066713907 67109336541562681600070861)
              ·
                refine ⟨25166001203086005600026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67109336541562681600070861 25166001203086005600026573)
                ·
                  refine ⟨9437250451157252100009965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25166001203086005600026573 9437250451157252100009965)
                  ·
                    refine ⟨3538968919183969537503737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9437250451157252100009965 3538968919183969537503737)
                    ·
                      refine ⟨2654226689387977153127803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3538968919183969537503737 2654226689387977153127803)
                      ·
                        rfl

theorem cell23_5169088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_5169088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169088 prefixEnd_5169088 := by exact prefixLift 5169088
  have htrace : WordTrace (prefixWord ++ tailWord_5169088) baseStart_5169088 baseEnd_5169088 := by
    simpa [prefixWord, tailWord_5169088, baseEnd_5169088] using wordTrace_append hprefix tailTrace_5169088
  have hstable : (prefixWord ++ tailWord_5169088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169088).length < 2 ^ (prefixWord ++ tailWord_5169088).sum := by decide
  have hdescent : baseEnd_5169088 < baseStart_5169088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169121 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_5169121 : Nat := 118140960795 + 5169121 * 2 ^ 59
def prefixEnd_5169121 : Nat := 4983230072969 + 3 ^ 40 * 5169121 * 2
def baseEnd_5169121 : Nat := 2654243634249575524015151

theorem tailTrace_5169121 : CollatzResearch.WordTrace tailWord_5169121 prefixEnd_5169121 2654243634249575524015151 := by
  unfold tailWord_5169121
  simp only [CollatzResearch.WordTrace]
  refine ⟨188533331506164907427371217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125688887670776604951580811 188533331506164907427371217)
  ·
    refine ⟨141399998629623680570528413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188533331506164907427371217 141399998629623680570528413)
    ·
      refine ⟨53024999486108880213948155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141399998629623680570528413 53024999486108880213948155)
      ·
        refine ⟨79537499229163320320922233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53024999486108880213948155 79537499229163320320922233)
        ·
          refine ⟨59653124421872490240691675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79537499229163320320922233 59653124421872490240691675)
          ·
            refine ⟨89479686632808735361037513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59653124421872490240691675 89479686632808735361037513)
            ·
              refine ⟨67109764974606551520778135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89479686632808735361037513 67109764974606551520778135)
              ·
                refine ⟨100664647461909827281167203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67109764974606551520778135 100664647461909827281167203)
                ·
                  refine ⟨150996971192864740921750805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100664647461909827281167203 150996971192864740921750805)
                  ·
                    refine ⟨7077983024665534730707069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 150996971192864740921750805 7077983024665534730707069)
                    ·
                      refine ⟨2654243634249575524015151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7077983024665534730707069 2654243634249575524015151)
                      ·
                        rfl

theorem cell23_5169121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_5169121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169121 prefixEnd_5169121 := by exact prefixLift 5169121
  have htrace : WordTrace (prefixWord ++ tailWord_5169121) baseStart_5169121 baseEnd_5169121 := by
    simpa [prefixWord, tailWord_5169121, baseEnd_5169121] using wordTrace_append hprefix tailTrace_5169121
  have hstable : (prefixWord ++ tailWord_5169121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169121).length < 2 ^ (prefixWord ++ tailWord_5169121).sum := by decide
  have hdescent : baseEnd_5169121 < baseStart_5169121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169151 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_5169151 : Nat := 118140960795 + 5169151 * 2 ^ 59
def prefixEnd_5169151 : Nat := 4983230072969 + 3 ^ 40 * 5169151 * 2
def baseEnd_5169151 : Nat := 2654259038669210406640013

theorem tailTrace_5169151 : CollatzResearch.WordTrace tailWord_5169151 prefixEnd_5169151 2654259038669210406640013 := by
  unfold tailWord_5169151
  simp only [CollatzResearch.WordTrace]
  refine ⟨188534425696056222550963307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125689617130704148367308871 188534425696056222550963307)
  ·
    refine ⟨282801638544084333826444961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188534425696056222550963307 282801638544084333826444961)
    ·
      refine ⟨212101228908063250369833721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282801638544084333826444961 212101228908063250369833721)
      ·
        refine ⟨159075921681047437777375291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212101228908063250369833721 159075921681047437777375291)
        ·
          refine ⟨238613882521571156666062937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159075921681047437777375291 238613882521571156666062937)
          ·
            refine ⟨178960411891178367499547203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238613882521571156666062937 178960411891178367499547203)
            ·
              refine ⟨268440617836767551249320805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178960411891178367499547203 268440617836767551249320805)
              ·
                refine ⟨50332615844393915859247651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268440617836767551249320805 50332615844393915859247651)
                ·
                  refine ⟨75498923766590873788871477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50332615844393915859247651 75498923766590873788871477)
                  ·
                    refine ⟨7078024103117894417706701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75498923766590873788871477 7078024103117894417706701)
                    ·
                      refine ⟨2654259038669210406640013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7078024103117894417706701 2654259038669210406640013)
                      ·
                        rfl

theorem cell23_5169151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_5169151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169151 prefixEnd_5169151 := by exact prefixLift 5169151
  have htrace : WordTrace (prefixWord ++ tailWord_5169151) baseStart_5169151 baseEnd_5169151 := by
    simpa [prefixWord, tailWord_5169151, baseEnd_5169151] using wordTrace_append hprefix tailTrace_5169151
  have hstable : (prefixWord ++ tailWord_5169151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169151).length < 2 ^ (prefixWord ++ tailWord_5169151).sum := by decide
  have hdescent : baseEnd_5169151 < baseStart_5169151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169171 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 4, 5]
def baseStart_5169171 : Nat := 118140960795 + 5169171 * 2 ^ 59
def prefixEnd_5169171 : Nat := 4983230072969 + 3 ^ 40 * 5169171 * 2
def baseEnd_5169171 : Nat := 884756436094100109463307

theorem tailTrace_5169171 : CollatzResearch.WordTrace tailWord_5169171 prefixEnd_5169171 884756436094100109463307 := by
  unfold tailWord_5169171
  simp only [CollatzResearch.WordTrace]
  refine ⟨188535155155983765966691367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125690103437322510644460911 188535155155983765966691367)
  ·
    refine ⟨282802732733975648950037051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188535155155983765966691367 282802732733975648950037051)
    ·
      refine ⟨424204099100963473425055577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282802732733975648950037051 424204099100963473425055577)
      ·
        refine ⟨318153074325722605068791683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424204099100963473425055577 318153074325722605068791683)
        ·
          refine ⟨477229611488583907603187525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318153074325722605068791683 477229611488583907603187525)
          ·
            refine ⟨89480552154109482675597661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 477229611488583907603187525 89480552154109482675597661)
            ·
              refine ⟨33555207057791056003349123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89480552154109482675597661 33555207057791056003349123)
              ·
                refine ⟨50332810586686584005023685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33555207057791056003349123 50332810586686584005023685)
                ·
                  refine ⟨9437401985003734500941941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50332810586686584005023685 9437401985003734500941941)
                  ·
                    refine ⟨884756436094100109463307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9437401985003734500941941 884756436094100109463307)
                    ·
                      rfl

theorem cell23_5169171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 5].length) (baseStart_5169171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169171 prefixEnd_5169171 := by exact prefixLift 5169171
  have htrace : WordTrace (prefixWord ++ tailWord_5169171) baseStart_5169171 baseEnd_5169171 := by
    simpa [prefixWord, tailWord_5169171, baseEnd_5169171] using wordTrace_append hprefix tailTrace_5169171
  have hstable : (prefixWord ++ tailWord_5169171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169171).length < 2 ^ (prefixWord ++ tailWord_5169171).sum := by decide
  have hdescent : baseEnd_5169171 < baseStart_5169171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169175 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 7]
def baseStart_5169175 : Nat := 118140960795 + 5169175 * 2 ^ 59
def prefixEnd_5169175 : Nat := 4983230072969 + 3 ^ 40 * 5169175 * 2
def baseEnd_5169175 : Nat := 294919040244990923637767

theorem tailTrace_5169175 : CollatzResearch.WordTrace tailWord_5169175 prefixEnd_5169175 294919040244990923637767 := by
  unfold tailWord_5169175
  simp only [CollatzResearch.WordTrace]
  refine ⟨188535301047969274649836979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125690200698646183099891319 188535301047969274649836979)
  ·
    refine ⟨282802951571953911974755469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188535301047969274649836979 282802951571953911974755469)
    ·
      refine ⟨106051106839482716990533301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282802951571953911974755469 106051106839482716990533301)
      ·
        refine ⟨9942291266201504717862497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106051106839482716990533301 9942291266201504717862497)
        ·
          refine ⟨7456718449651128538396873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9942291266201504717862497 7456718449651128538396873)
          ·
            refine ⟨5592538837238346403797655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7456718449651128538396873 5592538837238346403797655)
            ·
              refine ⟨8388808255857519605696483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592538837238346403797655 8388808255857519605696483)
              ·
                refine ⟨12583212383786279408544725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8388808255857519605696483 12583212383786279408544725)
                ·
                  refine ⟨294919040244990923637767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12583212383786279408544725 294919040244990923637767)
                  ·
                    rfl

theorem cell23_5169175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 7].length) (baseStart_5169175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169175 prefixEnd_5169175 := by exact prefixLift 5169175
  have htrace : WordTrace (prefixWord ++ tailWord_5169175) baseStart_5169175 baseEnd_5169175 := by
    simpa [prefixWord, tailWord_5169175, baseEnd_5169175] using wordTrace_append hprefix tailTrace_5169175
  have hstable : (prefixWord ++ tailWord_5169175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169175).length < 2 ^ (prefixWord ++ tailWord_5169175).sum := by decide
  have hdescent : baseEnd_5169175 < baseStart_5169175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169221 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_5169221 : Nat := 118140960795 + 5169221 * 2 ^ 59
def prefixEnd_5169221 : Nat := 4983230072969 + 3 ^ 40 * 5169221 * 2
def baseEnd_5169221 : Nat := 2654294982315025132764691

theorem tailTrace_5169221 : CollatzResearch.WordTrace tailWord_5169221 prefixEnd_5169221 2654294982315025132764691 := by
  unfold tailWord_5169221
  simp only [CollatzResearch.WordTrace]
  refine ⟨188536978805802624506011517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125691319203868416337341011 188536978805802624506011517)
  ·
    refine ⟨70701367052175984189754319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188536978805802624506011517 70701367052175984189754319)
    ·
      refine ⟨106052050578263976284631479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70701367052175984189754319 106052050578263976284631479)
      ·
        refine ⟨159078075867395964426947219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106052050578263976284631479 159078075867395964426947219)
        ·
          refine ⟨238617113801093946640420829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159078075867395964426947219 238617113801093946640420829)
          ·
            refine ⟨89481417675410229990157811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238617113801093946640420829 89481417675410229990157811)
            ·
              refine ⟨134222126513115344985236717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89481417675410229990157811 134222126513115344985236717)
              ·
                refine ⟨50333297442418254369463769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134222126513115344985236717 50333297442418254369463769)
                ·
                  refine ⟨37749973081813690777097827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50333297442418254369463769 37749973081813690777097827)
                  ·
                    refine ⟨56624959622720536165646741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37749973081813690777097827 56624959622720536165646741)
                    ·
                      refine ⟨2654294982315025132764691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56624959622720536165646741 2654294982315025132764691)
                      ·
                        rfl

theorem cell23_5169221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_5169221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169221 prefixEnd_5169221 := by exact prefixLift 5169221
  have htrace : WordTrace (prefixWord ++ tailWord_5169221) baseStart_5169221 baseEnd_5169221 := by
    simpa [prefixWord, tailWord_5169221, baseEnd_5169221] using wordTrace_append hprefix tailTrace_5169221
  have hstable : (prefixWord ++ tailWord_5169221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169221).length < 2 ^ (prefixWord ++ tailWord_5169221).sum := by decide
  have hdescent : baseEnd_5169221 < baseStart_5169221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169248 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 6]
def baseStart_5169248 : Nat := 118140960795 + 5169248 * 2 ^ 59
def prefixEnd_5169248 : Nat := 4983230072969 + 3 ^ 40 * 5169248 * 2
def baseEnd_5169248 : Nat := 294923205143632947458563

theorem tailTrace_5169248 : CollatzResearch.WordTrace tailWord_5169248 prefixEnd_5169248 294923205143632947458563 := by
  unfold tailWord_5169248
  simp only [CollatzResearch.WordTrace]
  refine ⟨94268981788352404058622199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125691975717803205411496265 94268981788352404058622199)
  ·
    refine ⟨141403472682528606087933299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94268981788352404058622199 141403472682528606087933299)
    ·
      refine ⟨212105209023792909131899949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141403472682528606087933299 212105209023792909131899949)
      ·
        refine ⟨79539453383922340924462481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212105209023792909131899949 79539453383922340924462481)
        ·
          refine ⟨59654590037941755693346861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79539453383922340924462481 59654590037941755693346861)
          ·
            refine ⟨22370471264228158385005073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59654590037941755693346861 22370471264228158385005073)
            ·
              refine ⟨16777853448171118788753805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22370471264228158385005073 16777853448171118788753805)
              ·
                refine ⟨6291695043064169545782677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16777853448171118788753805 6291695043064169545782677)
                ·
                  refine ⟨294923205143632947458563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6291695043064169545782677 294923205143632947458563)
                  ·
                    rfl

theorem cell23_5169248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_5169248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169248 prefixEnd_5169248 := by exact prefixLift 5169248
  have htrace : WordTrace (prefixWord ++ tailWord_5169248) baseStart_5169248 baseEnd_5169248 := by
    simpa [prefixWord, tailWord_5169248, baseEnd_5169248] using wordTrace_append hprefix tailTrace_5169248
  have hstable : (prefixWord ++ tailWord_5169248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169248).length < 2 ^ (prefixWord ++ tailWord_5169248).sum := by decide
  have hdescent : baseEnd_5169248 < baseStart_5169248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169291 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 10]
def baseStart_5169291 : Nat := 118140960795 + 5169291 * 2 ^ 59
def prefixEnd_5169291 : Nat := 4983230072969 + 3 ^ 40 * 5169291 * 2
def baseEnd_5169291 : Nat := 884776975320279952963123

theorem tailTrace_5169291 : CollatzResearch.WordTrace tailWord_5169291 prefixEnd_5169291 884776975320279952963123 := by
  unfold tailWord_5169291
  simp only [CollatzResearch.WordTrace]
  refine ⟨188539531915549026461059727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125693021277032684307373151 188539531915549026461059727)
  ·
    refine ⟨282809297873323539691589591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188539531915549026461059727 282809297873323539691589591)
    ·
      refine ⟨424213946809985309537384387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282809297873323539691589591 424213946809985309537384387)
      ·
        refine ⟨636320920214977964306076581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424213946809985309537384387 636320920214977964306076581)
        ·
          refine ⟨119310172540308368307389359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 636320920214977964306076581 119310172540308368307389359)
          ·
            refine ⟨178965258810462552461084039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119310172540308368307389359 178965258810462552461084039)
            ·
              refine ⟨268447888215693828691626059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178965258810462552461084039 268447888215693828691626059)
              ·
                refine ⟨402671832323540743037439089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268447888215693828691626059 402671832323540743037439089)
                ·
                  refine ⟨302003874242655557278079317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402671832323540743037439089 302003874242655557278079317)
                  ·
                    refine ⟨884776975320279952963123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 302003874242655557278079317 884776975320279952963123)
                    ·
                      rfl

theorem cell23_5169291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_5169291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169291 prefixEnd_5169291 := by exact prefixLift 5169291
  have htrace : WordTrace (prefixWord ++ tailWord_5169291) baseStart_5169291 baseEnd_5169291 := by
    simpa [prefixWord, tailWord_5169291, baseEnd_5169291] using wordTrace_append hprefix tailTrace_5169291
  have hstable : (prefixWord ++ tailWord_5169291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169291).length < 2 ^ (prefixWord ++ tailWord_5169291).sum := by decide
  have hdescent : baseEnd_5169291 < baseStart_5169291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169335 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_5169335 : Nat := 118140960795 + 5169335 * 2 ^ 59
def prefixEnd_5169335 : Nat := 4983230072969 + 3 ^ 40 * 5169335 * 2
def baseEnd_5169335 : Nat := 2654353519109637686739167

theorem tailTrace_5169335 : CollatzResearch.WordTrace tailWord_5169335 prefixEnd_5169335 2654353519109637686739167 := by
  unfold tailWord_5169335
  simp only [CollatzResearch.WordTrace]
  refine ⟨188541136727389621975661459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125694091151593081317107639 188541136727389621975661459)
  ·
    refine ⟨282811705091084432963492189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188541136727389621975661459 282811705091084432963492189)
    ·
      refine ⟨106054389409156662361309571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282811705091084432963492189 106054389409156662361309571)
      ·
        refine ⟨159081584113734993541964357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106054389409156662361309571 159081584113734993541964357)
        ·
          refine ⟨29827797021325311289118317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159081584113734993541964357 29827797021325311289118317)
          ·
            refine ⟨11185423882996991733419369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29827797021325311289118317 11185423882996991733419369)
            ·
              refine ⟨8389067912247743800064527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11185423882996991733419369 8389067912247743800064527)
              ·
                refine ⟨12583601868371615700096791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8389067912247743800064527 12583601868371615700096791)
                ·
                  refine ⟨18875402802557423550145187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12583601868371615700096791 18875402802557423550145187)
                  ·
                    refine ⟨28313104203836135325217781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18875402802557423550145187 28313104203836135325217781)
                    ·
                      refine ⟨2654353519109637686739167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28313104203836135325217781 2654353519109637686739167)
                      ·
                        rfl

theorem cell23_5169335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_5169335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169335 prefixEnd_5169335 := by exact prefixLift 5169335
  have htrace : WordTrace (prefixWord ++ tailWord_5169335) baseStart_5169335 baseEnd_5169335 := by
    simpa [prefixWord, tailWord_5169335, baseEnd_5169335] using wordTrace_append hprefix tailTrace_5169335
  have hstable : (prefixWord ++ tailWord_5169335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169335).length < 2 ^ (prefixWord ++ tailWord_5169335).sum := by decide
  have hdescent : baseEnd_5169335 < baseStart_5169335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169349 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 1, 2, 2]
def baseStart_5169349 : Nat := 118140960795 + 5169349 * 2 ^ 59
def prefixEnd_5169349 : Nat := 4983230072969 + 3 ^ 40 * 5169349 * 2
def baseEnd_5169349 : Nat := 2654360707838800631964103

theorem tailTrace_5169349 : CollatzResearch.WordTrace tailWord_5169349 prefixEnd_5169349 2654360707838800631964103 := by
  unfold tailWord_5169349
  simp only [CollatzResearch.WordTrace]
  refine ⟨188541647349338902366671101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125694431566225934911114067 188541647349338902366671101)
  ·
    refine ⟨70703117756002088387501663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188541647349338902366671101 70703117756002088387501663)
    ·
      refine ⟨106054676634003132581252495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70703117756002088387501663 106054676634003132581252495)
      ·
        refine ⟨159082014951004698871878743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106054676634003132581252495 159082014951004698871878743)
        ·
          refine ⟨238623022426507048307818115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159082014951004698871878743 238623022426507048307818115)
          ·
            refine ⟨357934533639760572461727173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238623022426507048307818115 357934533639760572461727173)
            ·
              refine ⟨67112725057455107336573845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357934533639760572461727173 67112725057455107336573845)
              ·
                refine ⟨3145908987068208156401899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67112725057455107336573845 3145908987068208156401899)
                ·
                  refine ⟨4718863480602312234602849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145908987068208156401899 4718863480602312234602849)
                  ·
                    refine ⟨3539147610451734175952137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4718863480602312234602849 3539147610451734175952137)
                    ·
                      refine ⟨2654360707838800631964103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539147610451734175952137 2654360707838800631964103)
                      ·
                        rfl

theorem cell23_5169349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_5169349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169349 prefixEnd_5169349 := by exact prefixLift 5169349
  have htrace : WordTrace (prefixWord ++ tailWord_5169349) baseStart_5169349 baseEnd_5169349 := by
    simpa [prefixWord, tailWord_5169349, baseEnd_5169349] using wordTrace_append hprefix tailTrace_5169349
  have hstable : (prefixWord ++ tailWord_5169349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169349).length < 2 ^ (prefixWord ++ tailWord_5169349).sum := by decide
  have hdescent : baseEnd_5169349 < baseStart_5169349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169366 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5169366 : Nat := 118140960795 + 5169366 * 2 ^ 59
def prefixEnd_5169366 : Nat := 4983230072969 + 3 ^ 40 * 5169366 * 2
def baseEnd_5169366 : Nat := 2654369437009927065451525

theorem tailTrace_5169366 : CollatzResearch.WordTrace tailWord_5169366 prefixEnd_5169366 2654369437009927065451525 := by
  unfold tailWord_5169366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783891711892332141877497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125694844926851542846693301 11783891711892332141877497)
  ·
    refine ⟨8837918783919249106408123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11783891711892332141877497 8837918783919249106408123)
    ·
      refine ⟨13256878175878873659612185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8837918783919249106408123 13256878175878873659612185)
      ·
        refine ⟨9942658631909155244709139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13256878175878873659612185 9942658631909155244709139)
        ·
          refine ⟨14913987947863732867063709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9942658631909155244709139 14913987947863732867063709)
          ·
            refine ⟨5592745480448899825148891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14913987947863732867063709 5592745480448899825148891)
            ·
              refine ⟨8389118220673349737723337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592745480448899825148891 8389118220673349737723337)
              ·
                refine ⟨6291838665505012303292503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8389118220673349737723337 6291838665505012303292503)
                ·
                  refine ⟨9437757998257518454938755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291838665505012303292503 9437757998257518454938755)
                  ·
                    refine ⟨14156636997386277682408133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9437757998257518454938755 14156636997386277682408133)
                    ·
                      refine ⟨2654369437009927065451525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14156636997386277682408133 2654369437009927065451525)
                      ·
                        rfl

theorem cell23_5169366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5169366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169366 prefixEnd_5169366 := by exact prefixLift 5169366
  have htrace : WordTrace (prefixWord ++ tailWord_5169366) baseStart_5169366 baseEnd_5169366 := by
    simpa [prefixWord, tailWord_5169366, baseEnd_5169366] using wordTrace_append hprefix tailTrace_5169366
  have hstable : (prefixWord ++ tailWord_5169366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169366).length < 2 ^ (prefixWord ++ tailWord_5169366).sum := by decide
  have hdescent : baseEnd_5169366 < baseStart_5169366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169392 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2]
def baseStart_5169392 : Nat := 118140960795 + 5169392 * 2 ^ 59
def prefixEnd_5169392 : Nat := 4983230072969 + 3 ^ 40 * 5169392 * 2
def baseEnd_5169392 : Nat := 2654382787506943963726405

theorem tailTrace_5169392 : CollatzResearch.WordTrace tailWord_5169392 prefixEnd_5169392 2654382787506943963726405 := by
  unfold tailWord_5169392
  simp only [CollatzResearch.WordTrace]
  refine ⟨94271607844091560355243215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125695477125455413806990953 94271607844091560355243215)
  ·
    refine ⟨141407411766137340532864823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94271607844091560355243215 141407411766137340532864823)
    ·
      refine ⟨212111117649206010799297235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141407411766137340532864823 212111117649206010799297235)
      ·
        refine ⟨318166676473809016198945853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212111117649206010799297235 318166676473809016198945853)
        ·
          refine ⟨119312503677678381074604695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318166676473809016198945853 119312503677678381074604695)
          ·
            refine ⟨178968755516517571611907043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119312503677678381074604695 178968755516517571611907043)
            ·
              refine ⟨268453133274776357417860565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178968755516517571611907043 268453133274776357417860565)
              ·
                refine ⟨6291870311127570876981107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 268453133274776357417860565 6291870311127570876981107)
                ·
                  refine ⟨9437805466691356315471661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6291870311127570876981107 9437805466691356315471661)
                  ·
                    refine ⟨3539177050009258618301873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9437805466691356315471661 3539177050009258618301873)
                    ·
                      refine ⟨2654382787506943963726405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539177050009258618301873 2654382787506943963726405)
                      ·
                        rfl

theorem cell23_5169392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2].length) (baseStart_5169392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169392 prefixEnd_5169392 := by exact prefixLift 5169392
  have htrace : WordTrace (prefixWord ++ tailWord_5169392) baseStart_5169392 baseEnd_5169392 := by
    simpa [prefixWord, tailWord_5169392, baseEnd_5169392] using wordTrace_append hprefix tailTrace_5169392
  have hstable : (prefixWord ++ tailWord_5169392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169392).length < 2 ^ (prefixWord ++ tailWord_5169392).sum := by decide
  have hdescent : baseEnd_5169392 < baseStart_5169392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169408 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_5169408 : Nat := 118140960795 + 5169408 * 2 ^ 59
def prefixEnd_5169408 : Nat := 4983230072969 + 3 ^ 40 * 5169408 * 2
def baseEnd_5169408 : Nat := 2654391003197415901126331

theorem tailTrace_5169408 : CollatzResearch.WordTrace tailWord_5169408 prefixEnd_5169408 2654391003197415901126331 := by
  unfold tailWord_5169408
  simp only [CollatzResearch.WordTrace]
  refine ⟨94271899628062577721534439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125695866170750103628712585 94271899628062577721534439)
  ·
    refine ⟨141407849442093866582301659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94271899628062577721534439 141407849442093866582301659)
    ·
      refine ⟨212111774163140799873452489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141407849442093866582301659 212111774163140799873452489)
      ·
        refine ⟨159083830622355599905089367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212111774163140799873452489 159083830622355599905089367)
        ·
          refine ⟨238625745933533399857634051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159083830622355599905089367 238625745933533399857634051)
          ·
            refine ⟨357938618900300099786451077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238625745933533399857634051 357938618900300099786451077)
            ·
              refine ⟨67113491043806268709959577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357938618900300099786451077 67113491043806268709959577)
              ·
                refine ⟨50335118282854701532469683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67113491043806268709959577 50335118282854701532469683)
                ·
                  refine ⟨75502677424282052298704525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50335118282854701532469683 75502677424282052298704525)
                  ·
                    refine ⟨28313504034105769612014197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75502677424282052298704525 28313504034105769612014197)
                    ·
                      refine ⟨2654391003197415901126331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28313504034105769612014197 2654391003197415901126331)
                      ·
                        rfl

theorem cell23_5169408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_5169408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169408 prefixEnd_5169408 := by exact prefixLift 5169408
  have htrace : WordTrace (prefixWord ++ tailWord_5169408) baseStart_5169408 baseEnd_5169408 := by
    simpa [prefixWord, tailWord_5169408, baseEnd_5169408] using wordTrace_append hprefix tailTrace_5169408
  have hstable : (prefixWord ++ tailWord_5169408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169408).length < 2 ^ (prefixWord ++ tailWord_5169408).sum := by decide
  have hdescent : baseEnd_5169408 < baseStart_5169408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169455 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_5169455 : Nat := 118140960795 + 5169455 * 2 ^ 59
def prefixEnd_5169455 : Nat := 4983230072969 + 3 ^ 40 * 5169455 * 2
def baseEnd_5169455 : Nat := 2654415136788177217238615

theorem tailTrace_5169455 : CollatzResearch.WordTrace tailWord_5169455 prefixEnd_5169455 2654415136788177217238615 := by
  unfold tailWord_5169455
  simp only [CollatzResearch.WordTrace]
  refine ⟨188545513486954882470029819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125697008991303254980019879 188545513486954882470029819)
  ·
    refine ⟨282818270230432323705044729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188545513486954882470029819 282818270230432323705044729)
    ·
      refine ⟨212113702672824242778783547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282818270230432323705044729 212113702672824242778783547)
      ·
        refine ⟨318170554009236364168175321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212113702672824242778783547 318170554009236364168175321)
        ·
          refine ⟨238627915506927273126131491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318170554009236364168175321 238627915506927273126131491)
          ·
            refine ⟨357941873260390909689197237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238627915506927273126131491 357941873260390909689197237)
            ·
              refine ⟨33557050618161647783362241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 357941873260390909689197237 33557050618161647783362241)
              ·
                refine ⟨25167787963621235837521681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33557050618161647783362241 25167787963621235837521681)
                ·
                  refine ⟨18875840972715926878141261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25167787963621235837521681 18875840972715926878141261)
                  ·
                    refine ⟨7078440364768472579302973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18875840972715926878141261 7078440364768472579302973)
                    ·
                      refine ⟨2654415136788177217238615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7078440364768472579302973 2654415136788177217238615)
                      ·
                        rfl

theorem cell23_5169455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_5169455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169455 prefixEnd_5169455 := by exact prefixLift 5169455
  have htrace : WordTrace (prefixWord ++ tailWord_5169455) baseStart_5169455 baseEnd_5169455 := by
    simpa [prefixWord, tailWord_5169455, baseEnd_5169455] using wordTrace_append hprefix tailTrace_5169455
  have hstable : (prefixWord ++ tailWord_5169455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169455).length < 2 ^ (prefixWord ++ tailWord_5169455).sum := by decide
  have hdescent : baseEnd_5169455 < baseStart_5169455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169473 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5169473 : Nat := 118140960795 + 5169473 * 2 ^ 59
def prefixEnd_5169473 : Nat := 4983230072969 + 3 ^ 40 * 5169473 * 2
def baseEnd_5169473 : Nat := 2654424379439958146813533

theorem tailTrace_5169473 : CollatzResearch.WordTrace tailWord_5169473 prefixEnd_5169473 2654424379439958146813533 := by
  unfold tailWord_5169473
  simp only [CollatzResearch.WordTrace]
  refine ⟨188546170000889671544185073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125697446667259781029456715 188546170000889671544185073)
  ·
    refine ⟨141409627500667253658138805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188546170000889671544185073 141409627500667253658138805)
    ·
      refine ⟨13257152578187555030450513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141409627500667253658138805 13257152578187555030450513)
      ·
        refine ⟨9942864433640666272837885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13257152578187555030450513 9942864433640666272837885)
        ·
          refine ⟨3728574162615249852314207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9942864433640666272837885 3728574162615249852314207)
          ·
            refine ⟨5592861243922874778471311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728574162615249852314207 5592861243922874778471311)
            ·
              refine ⟨8389291865884312167706967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592861243922874778471311 8389291865884312167706967)
              ·
                refine ⟨12583937798826468251560451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8389291865884312167706967 12583937798826468251560451)
                ·
                  refine ⟨18875906698239702377340677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12583937798826468251560451 18875906698239702377340677)
                  ·
                    refine ⟨3539232505919944195751377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18875906698239702377340677 3539232505919944195751377)
                    ·
                      refine ⟨2654424379439958146813533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539232505919944195751377 2654424379439958146813533)
                      ·
                        rfl

theorem cell23_5169473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5169473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169473 prefixEnd_5169473 := by exact prefixLift 5169473
  have htrace : WordTrace (prefixWord ++ tailWord_5169473) baseStart_5169473 baseEnd_5169473 := by
    simpa [prefixWord, tailWord_5169473, baseEnd_5169473] using wordTrace_append hprefix tailTrace_5169473
  have hstable : (prefixWord ++ tailWord_5169473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169473).length < 2 ^ (prefixWord ++ tailWord_5169473).sum := by decide
  have hdescent : baseEnd_5169473 < baseStart_5169473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169495 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_5169495 : Nat := 118140960795 + 5169495 * 2 ^ 59
def prefixEnd_5169495 : Nat := 4983230072969 + 3 ^ 40 * 5169495 * 2
def baseEnd_5169495 : Nat := 2654435676014357060738431

theorem tailTrace_5169495 : CollatzResearch.WordTrace tailWord_5169495 prefixEnd_5169495 2654435676014357060738431 := by
  unfold tailWord_5169495
  simp only [CollatzResearch.WordTrace]
  refine ⟨188546972406809969301485939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125697981604539979534323959 188546972406809969301485939)
  ·
    refine ⟨282820458610214953952228909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188546972406809969301485939 282820458610214953952228909)
    ·
      refine ⟨106057671978830607732085841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282820458610214953952228909 106057671978830607732085841)
      ·
        refine ⟨79543253984122955799064381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106057671978830607732085841 79543253984122955799064381)
        ·
          refine ⟨29828720244046108424649143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79543253984122955799064381 29828720244046108424649143)
          ·
            refine ⟨44743080366069162636973715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29828720244046108424649143 44743080366069162636973715)
            ·
              refine ⟨67114620549103743955460573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44743080366069162636973715 67114620549103743955460573)
              ·
                refine ⟨25167982705913903983297715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67114620549103743955460573 25167982705913903983297715)
                ·
                  refine ⟨37751974058870855974946573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25167982705913903983297715 37751974058870855974946573)
                  ·
                    refine ⟨14156990272076570990604965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37751974058870855974946573 14156990272076570990604965)
                    ·
                      refine ⟨2654435676014357060738431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14156990272076570990604965 2654435676014357060738431)
                      ·
                        rfl

theorem cell23_5169495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_5169495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169495 prefixEnd_5169495 := by exact prefixLift 5169495
  have htrace : WordTrace (prefixWord ++ tailWord_5169495) baseStart_5169495 baseEnd_5169495 := by
    simpa [prefixWord, tailWord_5169495, baseEnd_5169495] using wordTrace_append hprefix tailTrace_5169495
  have hstable : (prefixWord ++ tailWord_5169495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169495).length < 2 ^ (prefixWord ++ tailWord_5169495).sum := by decide
  have hdescent : baseEnd_5169495 < baseStart_5169495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169512 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5169512 : Nat := 118140960795 + 5169512 * 2 ^ 59
def prefixEnd_5169512 : Nat := 4983230072969 + 3 ^ 40 * 5169512 * 2
def baseEnd_5169512 : Nat := 2654444405185483494225853

theorem tailTrace_5169512 : CollatzResearch.WordTrace tailWord_5169512 prefixEnd_5169512 2654444405185483494225853 := by
  unfold tailWord_5169512
  simp only [CollatzResearch.WordTrace]
  refine ⟨94273796223874190602427395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125698394965165587469903193 94273796223874190602427395)
  ·
    refine ⟨141410694335811285903641093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94273796223874190602427395 141410694335811285903641093)
    ·
      refine ⟨26514505187964616106932705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141410694335811285903641093 26514505187964616106932705)
      ·
        refine ⟨19885878890973462080199529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26514505187964616106932705 19885878890973462080199529)
        ·
          refine ⟨14914409168230096560149647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19885878890973462080199529 14914409168230096560149647)
          ·
            refine ⟨22371613752345144840224471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14914409168230096560149647 22371613752345144840224471)
            ·
              refine ⟨33557420628517717260336707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22371613752345144840224471 33557420628517717260336707)
              ·
                refine ⟨50336130942776575890505061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33557420628517717260336707 50336130942776575890505061)
                ·
                  refine ⟨9438024551770607979469699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50336130942776575890505061 9438024551770607979469699)
                  ·
                    refine ⟨14157036827655911969204549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9438024551770607979469699 14157036827655911969204549)
                    ·
                      refine ⟨2654444405185483494225853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14157036827655911969204549 2654444405185483494225853)
                      ·
                        rfl

theorem cell23_5169512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5169512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169512 prefixEnd_5169512 := by exact prefixLift 5169512
  have htrace : WordTrace (prefixWord ++ tailWord_5169512) baseStart_5169512 baseEnd_5169512 := by
    simpa [prefixWord, tailWord_5169512, baseEnd_5169512] using wordTrace_append hprefix tailTrace_5169512
  have hstable : (prefixWord ++ tailWord_5169512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169512).length < 2 ^ (prefixWord ++ tailWord_5169512).sum := by decide
  have hdescent : baseEnd_5169512 < baseStart_5169512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169535 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 6]
def baseStart_5169535 : Nat := 118140960795 + 5169535 * 2 ^ 59
def prefixEnd_5169535 : Nat := 4983230072969 + 3 ^ 40 * 5169535 * 2
def baseEnd_5169535 : Nat := 294939579471170767137583

theorem tailTrace_5169535 : CollatzResearch.WordTrace tailWord_5169535 prefixEnd_5169535 294939579471170767137583 := by
  unfold tailWord_5169535
  simp only [CollatzResearch.WordTrace]
  refine ⟨188548431326665056132942059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125698954217776704088628039 188548431326665056132942059)
  ·
    refine ⟨282822646989997584199413089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188548431326665056132942059 282822646989997584199413089)
    ·
      refine ⟨212116985242498188149559817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282822646989997584199413089 212116985242498188149559817)
      ·
        refine ⟨159087738931873641112169863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212116985242498188149559817 159087738931873641112169863)
        ·
          refine ⟨238631608397810461668254795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159087738931873641112169863 238631608397810461668254795)
          ·
            refine ⟨357947412596715692502382193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238631608397810461668254795 357947412596715692502382193)
            ·
              refine ⟨268460559447536769376786645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357947412596715692502382193 268460559447536769376786645)
              ·
                refine ⟨6292044362051643032268437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 268460559447536769376786645 6292044362051643032268437)
                ·
                  refine ⟨294939579471170767137583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6292044362051643032268437 294939579471170767137583)
                  ·
                    rfl

theorem cell23_5169535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 6].length) (baseStart_5169535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169535 prefixEnd_5169535 := by exact prefixLift 5169535
  have htrace : WordTrace (prefixWord ++ tailWord_5169535) baseStart_5169535 baseEnd_5169535 := by
    simpa [prefixWord, tailWord_5169535, baseEnd_5169535] using wordTrace_append hprefix tailTrace_5169535
  have hstable : (prefixWord ++ tailWord_5169535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169535).length < 2 ^ (prefixWord ++ tailWord_5169535).sum := by decide
  have hdescent : baseEnd_5169535 < baseStart_5169535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169546 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5169546 : Nat := 118140960795 + 5169546 * 2 ^ 59
def prefixEnd_5169546 : Nat := 4983230072969 + 3 ^ 40 * 5169546 * 2
def baseEnd_5169546 : Nat := 2654461863527736361200697

theorem tailTrace_5169546 : CollatzResearch.WordTrace tailWord_5169546 prefixEnd_5169546 2654461863527736361200697 := by
  unfold tailWord_5169546
  simp only [CollatzResearch.WordTrace]
  refine ⟨47137208132406301252898123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125699221686416803341061661 47137208132406301252898123)
  ·
    refine ⟨70705812198609451879347185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47137208132406301252898123 70705812198609451879347185)
    ·
      refine ⟨53029359148957088909510389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70705812198609451879347185 53029359148957088909510389)
      ·
        refine ⟨4971502420214727085266599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53029359148957088909510389 4971502420214727085266599)
        ·
          refine ⟨7457253630322090627899899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971502420214727085266599 7457253630322090627899899)
          ·
            refine ⟨11185880445483135941849849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457253630322090627899899 11185880445483135941849849)
            ·
              refine ⟨8389410334112351956387387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11185880445483135941849849 8389410334112351956387387)
              ·
                refine ⟨12584115501168527934581081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8389410334112351956387387 12584115501168527934581081)
                ·
                  refine ⟨9438086625876395950935811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12584115501168527934581081 9438086625876395950935811)
                  ·
                    refine ⟨14157129938814593926403717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9438086625876395950935811 14157129938814593926403717)
                    ·
                      refine ⟨2654461863527736361200697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14157129938814593926403717 2654461863527736361200697)
                      ·
                        rfl

theorem cell23_5169546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5169546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169546 prefixEnd_5169546 := by exact prefixLift 5169546
  have htrace : WordTrace (prefixWord ++ tailWord_5169546) baseStart_5169546 baseEnd_5169546 := by
    simpa [prefixWord, tailWord_5169546, baseEnd_5169546] using wordTrace_append hprefix tailTrace_5169546
  have hstable : (prefixWord ++ tailWord_5169546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169546).length < 2 ^ (prefixWord ++ tailWord_5169546).sum := by decide
  have hdescent : baseEnd_5169546 < baseStart_5169546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169566 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5169566 : Nat := 118140960795 + 5169566 * 2 ^ 59
def prefixEnd_5169566 : Nat := 4983230072969 + 3 ^ 40 * 5169566 * 2
def baseEnd_5169566 : Nat := 2654472133140826282950605

theorem tailTrace_5169566 : CollatzResearch.WordTrace tailWord_5169566 prefixEnd_5169566 2654472133140826282950605 := by
  unfold tailWord_5169566
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568695248694093553415069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125699707993035165618213701 23568695248694093553415069)
  ·
    refine ⟨8838260718260285082530651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23568695248694093553415069 8838260718260285082530651)
    ·
      refine ⟨13257391077390427623795977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8838260718260285082530651 13257391077390427623795977)
      ·
        refine ⟨9943043308042820717846983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13257391077390427623795977 9943043308042820717846983)
        ·
          refine ⟨14914564962064231076770475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943043308042820717846983 14914564962064231076770475)
          ·
            refine ⟨22371847443096346615155713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14914564962064231076770475 22371847443096346615155713)
            ·
              refine ⟨16778885582322259961366785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22371847443096346615155713 16778885582322259961366785)
              ·
                refine ⟨12584164186741694971025089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16778885582322259961366785 12584164186741694971025089)
                ·
                  refine ⟨9438123140056271228268817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12584164186741694971025089 9438123140056271228268817)
                  ·
                    refine ⟨7078592355042203421201613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9438123140056271228268817 7078592355042203421201613)
                    ·
                      refine ⟨2654472133140826282950605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7078592355042203421201613 2654472133140826282950605)
                      ·
                        rfl

theorem cell23_5169566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5169566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169566 prefixEnd_5169566 := by exact prefixLift 5169566
  have htrace : WordTrace (prefixWord ++ tailWord_5169566) baseStart_5169566 baseEnd_5169566 := by
    simpa [prefixWord, tailWord_5169566, baseEnd_5169566] using wordTrace_append hprefix tailTrace_5169566
  have hstable : (prefixWord ++ tailWord_5169566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169566).length < 2 ^ (prefixWord ++ tailWord_5169566).sum := by decide
  have hdescent : baseEnd_5169566 < baseStart_5169566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169596 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5169596 : Nat := 118140960795 + 5169596 * 2 ^ 59
def prefixEnd_5169596 : Nat := 4983230072969 + 3 ^ 40 * 5169596 * 2
def baseEnd_5169596 : Nat := 2654487537560461165575467

theorem tailTrace_5169596 : CollatzResearch.WordTrace tailWord_5169596 prefixEnd_5169596 2654487537560461165575467 := by
  unfold tailWord_5169596
  simp only [CollatzResearch.WordTrace]
  refine ⟨94275328089722031775456321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125700437452962709033941761 94275328089722031775456321)
  ·
    refine ⟨70706496067291523831592241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94275328089722031775456321 70706496067291523831592241)
    ·
      refine ⟨53029872050468642873694181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70706496067291523831592241 53029872050468642873694181)
      ·
        refine ⟨9943101009462870538817659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53029872050468642873694181 9943101009462870538817659)
        ·
          refine ⟨14914651514194305808226489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943101009462870538817659 14914651514194305808226489)
          ·
            refine ⟨11185988635645729356169867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14914651514194305808226489 11185988635645729356169867)
            ·
              refine ⟨16778982953468594034254801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11185988635645729356169867 16778982953468594034254801)
              ·
                refine ⟨12584237215101445525691101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16778982953468594034254801 12584237215101445525691101)
                ·
                  refine ⟨4719088955663042072134163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12584237215101445525691101 4719088955663042072134163)
                  ·
                    refine ⟨7078633433494563108201245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4719088955663042072134163 7078633433494563108201245)
                    ·
                      refine ⟨2654487537560461165575467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7078633433494563108201245 2654487537560461165575467)
                      ·
                        rfl

theorem cell23_5169596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5169596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169596 prefixEnd_5169596 := by exact prefixLift 5169596
  have htrace : WordTrace (prefixWord ++ tailWord_5169596) baseStart_5169596 baseEnd_5169596 := by
    simpa [prefixWord, tailWord_5169596, baseEnd_5169596] using wordTrace_append hprefix tailTrace_5169596
  have hstable : (prefixWord ++ tailWord_5169596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169596).length < 2 ^ (prefixWord ++ tailWord_5169596).sum := by decide
  have hdescent : baseEnd_5169596 < baseStart_5169596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169615 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_5169615 : Nat := 118140960795 + 5169615 * 2 ^ 59
def prefixEnd_5169615 : Nat := 4983230072969 + 3 ^ 40 * 5169615 * 2
def baseEnd_5169615 : Nat := 2654497293692896591237879

theorem tailTrace_5169615 : CollatzResearch.WordTrace tailWord_5169615 prefixEnd_5169615 2654497293692896591237879 := by
  unfold tailWord_5169615
  simp only [CollatzResearch.WordTrace]
  refine ⟨188551349166375229795854299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125700899444250153197236199 188551349166375229795854299)
  ·
    refine ⟨282827023749562844693781449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188551349166375229795854299 282827023749562844693781449)
    ·
      refine ⟨212120267812172133520336087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282827023749562844693781449 212120267812172133520336087)
      ·
        refine ⟨318180401718258200280504131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212120267812172133520336087 318180401718258200280504131)
        ·
          refine ⟨477270602577387300420756197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318180401718258200280504131 477270602577387300420756197)
          ·
            refine ⟨89488237983260118828891787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 477270602577387300420756197 89488237983260118828891787)
            ·
              refine ⟨134232356974890178243337681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89488237983260118828891787 134232356974890178243337681)
              ·
                refine ⟨100674267731167633682503261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134232356974890178243337681 100674267731167633682503261)
                ·
                  refine ⟨37752850399187862630938723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100674267731167633682503261 37752850399187862630938723)
                  ·
                    refine ⟨56629275598781793946408085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37752850399187862630938723 56629275598781793946408085)
                    ·
                      refine ⟨2654497293692896591237879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56629275598781793946408085 2654497293692896591237879)
                      ·
                        rfl

theorem cell23_5169615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_5169615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169615 prefixEnd_5169615 := by exact prefixLift 5169615
  have htrace : WordTrace (prefixWord ++ tailWord_5169615) baseStart_5169615 baseEnd_5169615 := by
    simpa [prefixWord, tailWord_5169615, baseEnd_5169615] using wordTrace_append hprefix tailTrace_5169615
  have hstable : (prefixWord ++ tailWord_5169615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169615).length < 2 ^ (prefixWord ++ tailWord_5169615).sum := by decide
  have hdescent : baseEnd_5169615 < baseStart_5169615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169625 : List Nat := [1, 2, 1, 2, 4, 1, 12]
def baseStart_5169625 : Nat := 118140960795 + 5169625 * 2 ^ 59
def prefixEnd_5169625 : Nat := 4983230072969 + 3 ^ 40 * 5169625 * 2
def baseEnd_5169625 : Nat := 32771634919746192001393

theorem tailTrace_5169625 : CollatzResearch.WordTrace tailWord_5169625 prefixEnd_5169625 32771634919746192001393 := by
  unfold tailWord_5169625
  simp only [CollatzResearch.WordTrace]
  refine ⟨188551713896339001503718329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125701142597559334335812219 188551713896339001503718329)
  ·
    refine ⟨141413785422254251127788747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188551713896339001503718329 141413785422254251127788747)
    ·
      refine ⟨212120678133381376691683121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141413785422254251127788747 212120678133381376691683121)
      ·
        refine ⟨159090508600036032518762341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212120678133381376691683121 159090508600036032518762341)
        ·
          refine ⟨29829470362506756097267939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159090508600036032518762341 29829470362506756097267939)
          ·
            refine ⟨44744205543760134145901909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29829470362506756097267939 44744205543760134145901909)
            ·
              refine ⟨32771634919746192001393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44744205543760134145901909 32771634919746192001393)
              ·
                rfl

theorem cell23_5169625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 12].length) (baseStart_5169625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169625 prefixEnd_5169625 := by exact prefixLift 5169625
  have htrace : WordTrace (prefixWord ++ tailWord_5169625) baseStart_5169625 baseEnd_5169625 := by
    simpa [prefixWord, tailWord_5169625, baseEnd_5169625] using wordTrace_append hprefix tailTrace_5169625
  have hstable : (prefixWord ++ tailWord_5169625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169625).length < 2 ^ (prefixWord ++ tailWord_5169625).sum := by decide
  have hdescent : baseEnd_5169625 < baseStart_5169625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169629 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_5169629 : Nat := 118140960795 + 5169629 * 2 ^ 59
def prefixEnd_5169629 : Nat := 4983230072969 + 3 ^ 40 * 5169629 * 2
def baseEnd_5169629 : Nat := 884834827474019845487605

theorem tailTrace_5169629 : CollatzResearch.WordTrace tailWord_5169629 prefixEnd_5169629 884834827474019845487605 := by
  unfold tailWord_5169629
  simp only [CollatzResearch.WordTrace]
  refine ⟨188551859788324510186863941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125701239858883006791242627 188551859788324510186863941)
  ·
    refine ⟨35353473710310845660036989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188551859788324510186863941 35353473710310845660036989)
    ·
      refine ⟨13257552641366567122513871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35353473710310845660036989 13257552641366567122513871)
      ·
        refine ⟨19886328962049850683770807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13257552641366567122513871 19886328962049850683770807)
        ·
          refine ⟨29829493443074776025656211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19886328962049850683770807 29829493443074776025656211)
          ·
            refine ⟨44744240164612164038484317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29829493443074776025656211 44744240164612164038484317)
            ·
              refine ⟨16779090061729561514431619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44744240164612164038484317 16779090061729561514431619)
              ·
                refine ⟨25168635092594342271647429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779090061729561514431619 25168635092594342271647429)
                ·
                  refine ⟨4719119079861439175933893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25168635092594342271647429 4719119079861439175933893)
                  ·
                    refine ⟨884834827474019845487605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4719119079861439175933893 884834827474019845487605)
                    ·
                      rfl

theorem cell23_5169629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_5169629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169629 prefixEnd_5169629 := by exact prefixLift 5169629
  have htrace : WordTrace (prefixWord ++ tailWord_5169629) baseStart_5169629 baseEnd_5169629 := by
    simpa [prefixWord, tailWord_5169629, baseEnd_5169629] using wordTrace_append hprefix tailTrace_5169629
  have hstable : (prefixWord ++ tailWord_5169629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169629).length < 2 ^ (prefixWord ++ tailWord_5169629).sum := by decide
  have hdescent : baseEnd_5169629 < baseStart_5169629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169653 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5169653 : Nat := 118140960795 + 5169653 * 2 ^ 59
def prefixEnd_5169653 : Nat := 4983230072969 + 3 ^ 40 * 5169653 * 2
def baseEnd_5169653 : Nat := 2654516805957767442562705

theorem tailTrace_5169653 : CollatzResearch.WordTrace tailWord_5169653 prefixEnd_5169653 2654516805957767442562705 := by
  unfold tailWord_5169653
  simp only [CollatzResearch.WordTrace]
  refine ⟨188552735140237562285737613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125701823426825041523825075 188552735140237562285737613)
  ·
    refine ⟨70707275677589085857151605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188552735140237562285737613 70707275677589085857151605)
    ·
      refine ⟨6628807094773976799107963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70707275677589085857151605 6628807094773976799107963)
      ·
        refine ⟨9943210642160965198661945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628807094773976799107963 9943210642160965198661945)
        ·
          refine ⟨7457407981620723898996459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9943210642160965198661945 7457407981620723898996459)
          ·
            refine ⟨11186111972431085848494689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457407981620723898996459 11186111972431085848494689)
            ·
              refine ⟨8389583979323314386371017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11186111972431085848494689 8389583979323314386371017)
              ·
                refine ⟨6292187984492485789778263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8389583979323314386371017 6292187984492485789778263)
                ·
                  refine ⟨9438281976738728684667395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292187984492485789778263 9438281976738728684667395)
                  ·
                    refine ⟨14157422965108093027001093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9438281976738728684667395 14157422965108093027001093)
                    ·
                      refine ⟨2654516805957767442562705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14157422965108093027001093 2654516805957767442562705)
                      ·
                        rfl

theorem cell23_5169653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5169653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169653 prefixEnd_5169653 := by exact prefixLift 5169653
  have htrace : WordTrace (prefixWord ++ tailWord_5169653) baseStart_5169653 baseEnd_5169653 := by
    simpa [prefixWord, tailWord_5169653, baseEnd_5169653] using wordTrace_append hprefix tailTrace_5169653
  have hstable : (prefixWord ++ tailWord_5169653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169653).length < 2 ^ (prefixWord ++ tailWord_5169653).sum := by decide
  have hdescent : baseEnd_5169653 < baseStart_5169653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169655 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 9]
def baseStart_5169655 : Nat := 118140960795 + 5169655 * 2 ^ 59
def prefixEnd_5169655 : Nat := 4983230072969 + 3 ^ 40 * 5169655 * 2
def baseEnd_5169655 : Nat := 884839277639692144912565

theorem tailTrace_5169655 : CollatzResearch.WordTrace tailWord_5169655 prefixEnd_5169655 884839277639692144912565 := by
  unfold tailWord_5169655
  simp only [CollatzResearch.WordTrace]
  refine ⟨188552808086230316627310419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125701872057486877751540279 188552808086230316627310419)
  ·
    refine ⟨282829212129345474940965629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188552808086230316627310419 282829212129345474940965629)
    ·
      refine ⟨106060954548504553102862111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282829212129345474940965629 106060954548504553102862111)
      ·
        refine ⟨159091431822756829654293167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106060954548504553102862111 159091431822756829654293167)
        ·
          refine ⟨238637147734135244481439751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159091431822756829654293167 238637147734135244481439751)
          ·
            refine ⟨357955721601202866722159627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238637147734135244481439751 357955721601202866722159627)
            ·
              refine ⟨536933582401804300083239441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357955721601202866722159627 536933582401804300083239441)
              ·
                refine ⟨402700186801353225062429581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536933582401804300083239441 402700186801353225062429581)
                ·
                  refine ⟨151012570050507459398411093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402700186801353225062429581 151012570050507459398411093)
                  ·
                    refine ⟨884839277639692144912565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151012570050507459398411093 884839277639692144912565)
                    ·
                      rfl

theorem cell23_5169655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_5169655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169655 prefixEnd_5169655 := by exact prefixLift 5169655
  have htrace : WordTrace (prefixWord ++ tailWord_5169655) baseStart_5169655 baseEnd_5169655 := by
    simpa [prefixWord, tailWord_5169655, baseEnd_5169655] using wordTrace_append hprefix tailTrace_5169655
  have hstable : (prefixWord ++ tailWord_5169655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169655).length < 2 ^ (prefixWord ++ tailWord_5169655).sum := by decide
  have hdescent : baseEnd_5169655 < baseStart_5169655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169669 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_5169669 : Nat := 118140960795 + 5169669 * 2 ^ 59
def prefixEnd_5169669 : Nat := 4983230072969 + 3 ^ 40 * 5169669 * 2
def baseEnd_5169669 : Nat := 2654525021648239379962631

theorem tailTrace_5169669 : CollatzResearch.WordTrace tailWord_5169669 prefixEnd_5169669 2654525021648239379962631 := by
  unfold tailWord_5169669
  simp only [CollatzResearch.WordTrace]
  refine ⟨188553318708179597018320061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125702212472119731345546707 188553318708179597018320061)
  ·
    refine ⟨70707494515567348881870023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188553318708179597018320061 70707494515567348881870023)
    ·
      refine ⟨106061241773351023322805035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70707494515567348881870023 106061241773351023322805035)
      ·
        refine ⟨159091862660026534984207553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106061241773351023322805035 159091862660026534984207553)
        ·
          refine ⟨119318896995019901238155665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159091862660026534984207553 119318896995019901238155665)
          ·
            refine ⟨89489172746264925928616749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119318896995019901238155665 89489172746264925928616749)
            ·
              refine ⟨33558439779849347223231281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89489172746264925928616749 33558439779849347223231281)
              ·
                refine ⟨25168829834887010417423461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33558439779849347223231281 25168829834887010417423461)
                ·
                  refine ⟨4719155594041314453266899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25168829834887010417423461 4719155594041314453266899)
                  ·
                    refine ⟨7078733391061971679900349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4719155594041314453266899 7078733391061971679900349)
                    ·
                      refine ⟨2654525021648239379962631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7078733391061971679900349 2654525021648239379962631)
                      ·
                        rfl

theorem cell23_5169669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_5169669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169669 prefixEnd_5169669 := by exact prefixLift 5169669
  have htrace : WordTrace (prefixWord ++ tailWord_5169669) baseStart_5169669 baseEnd_5169669 := by
    simpa [prefixWord, tailWord_5169669, baseEnd_5169669] using wordTrace_append hprefix tailTrace_5169669
  have hstable : (prefixWord ++ tailWord_5169669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169669).length < 2 ^ (prefixWord ++ tailWord_5169669).sum := by decide
  have hdescent : baseEnd_5169669 < baseStart_5169669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169670 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5169670 : Nat := 118140960795 + 5169670 * 2 ^ 59
def prefixEnd_5169670 : Nat := 4983230072969 + 3 ^ 40 * 5169670 * 2
def baseEnd_5169670 : Nat := 2654525535128893876050127

theorem tailTrace_5169670 : CollatzResearch.WordTrace tailWord_5169670 prefixEnd_5169670 2654525535128893876050127 := by
  unfold tailWord_5169670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5892292349411749193409577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125702236787450649459404309 5892292349411749193409577)
  ·
    refine ⟨4419219262058811895057183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5892292349411749193409577 4419219262058811895057183)
    ·
      refine ⟨6628828893088217842585775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4419219262058811895057183 6628828893088217842585775)
      ·
        refine ⟨9943243339632326763878663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628828893088217842585775 9943243339632326763878663)
        ·
          refine ⟨14914865009448490145817995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9943243339632326763878663 14914865009448490145817995)
          ·
            refine ⟨22372297514172735218726993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14914865009448490145817995 22372297514172735218726993)
            ·
              refine ⟨16779223135629551414045245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22372297514172735218726993 16779223135629551414045245)
              ·
                refine ⟨6292208675861081780266967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16779223135629551414045245 6292208675861081780266967)
                ·
                  refine ⟨9438313013791622670400451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292208675861081780266967 9438313013791622670400451)
                  ·
                    refine ⟨14157469520687434005600677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9438313013791622670400451 14157469520687434005600677)
                    ·
                      refine ⟨2654525535128893876050127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14157469520687434005600677 2654525535128893876050127)
                      ·
                        rfl

theorem cell23_5169670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5169670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169670 prefixEnd_5169670 := by exact prefixLift 5169670
  have htrace : WordTrace (prefixWord ++ tailWord_5169670) baseStart_5169670 baseEnd_5169670 := by
    simpa [prefixWord, tailWord_5169670, baseEnd_5169670] using wordTrace_append hprefix tailTrace_5169670
  have hstable : (prefixWord ++ tailWord_5169670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169670).length < 2 ^ (prefixWord ++ tailWord_5169670).sum := by decide
  have hdescent : baseEnd_5169670 < baseStart_5169670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169687 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5169687 : Nat := 118140960795 + 5169687 * 2 ^ 59
def prefixEnd_5169687 : Nat := 4983230072969 + 3 ^ 40 * 5169687 * 2
def baseEnd_5169687 : Nat := 2654534264300020309537549

theorem tailTrace_5169687 : CollatzResearch.WordTrace tailWord_5169687 prefixEnd_5169687 2654534264300020309537549 := by
  unfold tailWord_5169687
  simp only [CollatzResearch.WordTrace]
  refine ⟨188553975222114386092475315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125702650148076257394983543 188553975222114386092475315)
  ·
    refine ⟨282830962833171579138712973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188553975222114386092475315 282830962833171579138712973)
    ·
      refine ⟨106061611062439342177017365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282830962833171579138712973 106061611062439342177017365)
      ·
        refine ⟨4971638018551844164547689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106061611062439342177017365 4971638018551844164547689)
        ·
          refine ⟨3728728513913883123410767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4971638018551844164547689 3728728513913883123410767)
          ·
            refine ⟨5593092770870824685116151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728728513913883123410767 5593092770870824685116151)
            ·
              refine ⟨8389639156306237027674227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593092770870824685116151 8389639156306237027674227)
              ·
                refine ⟨12584458734459355541511341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8389639156306237027674227 12584458734459355541511341)
                ·
                  refine ⟨4719172025422258328066753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12584458734459355541511341 4719172025422258328066753)
                  ·
                    refine ⟨3539379019066693746050065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719172025422258328066753 3539379019066693746050065)
                    ·
                      refine ⟨2654534264300020309537549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539379019066693746050065 2654534264300020309537549)
                      ·
                        rfl

theorem cell23_5169687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5169687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169687 prefixEnd_5169687 := by exact prefixLift 5169687
  have htrace : WordTrace (prefixWord ++ tailWord_5169687) baseStart_5169687 baseEnd_5169687 := by
    simpa [prefixWord, tailWord_5169687, baseEnd_5169687] using wordTrace_append hprefix tailTrace_5169687
  have hstable : (prefixWord ++ tailWord_5169687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169687).length < 2 ^ (prefixWord ++ tailWord_5169687).sum := by decide
  have hdescent : baseEnd_5169687 < baseStart_5169687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169712 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_5169712 : Nat := 118140960795 + 5169712 * 2 ^ 59
def prefixEnd_5169712 : Nat := 4983230072969 + 3 ^ 40 * 5169712 * 2
def baseEnd_5169712 : Nat := 2654547101316382711724933

theorem tailTrace_5169712 : CollatzResearch.WordTrace tailWord_5169712 prefixEnd_5169712 2654547101316382711724933 := by
  unfold tailWord_5169712
  simp only [CollatzResearch.WordTrace]
  refine ⟨94277443523511907681067695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125703258031349210241423593 94277443523511907681067695)
  ·
    refine ⟨141416165285267861521601543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94277443523511907681067695 141416165285267861521601543)
    ·
      refine ⟨212124247927901792282402315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141416165285267861521601543 212124247927901792282402315)
      ·
        refine ⟨318186371891852688423603473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212124247927901792282402315 318186371891852688423603473)
        ·
          refine ⟨238639778918889516317702605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318186371891852688423603473 238639778918889516317702605)
          ·
            refine ⟨89489917094583568619138477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238639778918889516317702605 89489917094583568619138477)
            ·
              refine ⟨33558718910468838232176929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89489917094583568619138477 33558718910468838232176929)
              ·
                refine ⟨25169039182851628674132697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33558718910468838232176929 25169039182851628674132697)
                ·
                  refine ⟨18876779387138721505599523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25169039182851628674132697 18876779387138721505599523)
                  ·
                    refine ⟨28315169080708082258399285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18876779387138721505599523 28315169080708082258399285)
                    ·
                      refine ⟨2654547101316382711724933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28315169080708082258399285 2654547101316382711724933)
                      ·
                        rfl

theorem cell23_5169712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_5169712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169712 prefixEnd_5169712 := by exact prefixLift 5169712
  have htrace : WordTrace (prefixWord ++ tailWord_5169712) baseStart_5169712 baseEnd_5169712 := by
    simpa [prefixWord, tailWord_5169712, baseEnd_5169712] using wordTrace_append hprefix tailTrace_5169712
  have hstable : (prefixWord ++ tailWord_5169712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169712).length < 2 ^ (prefixWord ++ tailWord_5169712).sum := by decide
  have hdescent : baseEnd_5169712 < baseStart_5169712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169729 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5169729 : Nat := 118140960795 + 5169729 * 2 ^ 59
def prefixEnd_5169729 : Nat := 4983230072969 + 3 ^ 40 * 5169729 * 2
def baseEnd_5169729 : Nat := 2654555830487509145212355

theorem tailTrace_5169729 : CollatzResearch.WordTrace tailWord_5169729 prefixEnd_5169729 2654555830487509145212355 := by
  unfold tailWord_5169729
  simp only [CollatzResearch.WordTrace]
  refine ⟨188555507087962227265504241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125703671391974818177002827 188555507087962227265504241)
  ·
    refine ⟨141416630315971670449128181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188555507087962227265504241 141416630315971670449128181)
    ·
      refine ⟨13257809092122344104605767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141416630315971670449128181 13257809092122344104605767)
      ·
        refine ⟨19886713638183516156908651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13257809092122344104605767 19886713638183516156908651)
        ·
          refine ⟨29830070457275274235362977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19886713638183516156908651 29830070457275274235362977)
          ·
            refine ⟨22372552842956455676522233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29830070457275274235362977 22372552842956455676522233)
            ·
              refine ⟨16779414632217341757391675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22372552842956455676522233 16779414632217341757391675)
              ·
                refine ⟨25169121948326012636087513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779414632217341757391675 25169121948326012636087513)
                ·
                  refine ⟨18876841461244509477065635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25169121948326012636087513 18876841461244509477065635)
                  ·
                    refine ⟨28315262191866764215598453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18876841461244509477065635 28315262191866764215598453)
                    ·
                      refine ⟨2654555830487509145212355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28315262191866764215598453 2654555830487509145212355)
                      ·
                        rfl

theorem cell23_5169729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5169729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169729 prefixEnd_5169729 := by exact prefixLift 5169729
  have htrace : WordTrace (prefixWord ++ tailWord_5169729) baseStart_5169729 baseEnd_5169729 := by
    simpa [prefixWord, tailWord_5169729, baseEnd_5169729] using wordTrace_append hprefix tailTrace_5169729
  have hstable : (prefixWord ++ tailWord_5169729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169729).length < 2 ^ (prefixWord ++ tailWord_5169729).sum := by decide
  have hdescent : baseEnd_5169729 < baseStart_5169729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169742 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_5169742 : Nat := 118140960795 + 5169742 * 2 ^ 59
def prefixEnd_5169742 : Nat := 4983230072969 + 3 ^ 40 * 5169742 * 2
def baseEnd_5169742 : Nat := 2654562505736017594349795

theorem tailTrace_5169742 : CollatzResearch.WordTrace tailWord_5169742 prefixEnd_5169742 2654562505736017594349795 := by
  unfold tailWord_5169742
  simp only [CollatzResearch.WordTrace]
  refine ⟨23569497654614391310715935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125703987491276753657151653 23569497654614391310715935)
  ·
    refine ⟨35354246481921586966073903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23569497654614391310715935 35354246481921586966073903)
    ·
      refine ⟨53031369722882380449110855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35354246481921586966073903 53031369722882380449110855)
      ·
        refine ⟨79547054584323570673666283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53031369722882380449110855 79547054584323570673666283)
        ·
          refine ⟨119320581876485356010499425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79547054584323570673666283 119320581876485356010499425)
          ·
            refine ⟨89490436407364017007874569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119320581876485356010499425 89490436407364017007874569)
            ·
              refine ⟨67117827305523012755905927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89490436407364017007874569 67117827305523012755905927)
              ·
                refine ⟨100676740958284519133858891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67117827305523012755905927 100676740958284519133858891)
                ·
                  refine ⟨151015111437426778700788337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100676740958284519133858891 151015111437426778700788337)
                  ·
                    refine ⟨113261333578070084025591253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151015111437426778700788337 113261333578070084025591253)
                    ·
                      refine ⟨2654562505736017594349795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113261333578070084025591253 2654562505736017594349795)
                      ·
                        rfl

theorem cell23_5169742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_5169742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169742 prefixEnd_5169742 := by exact prefixLift 5169742
  have htrace : WordTrace (prefixWord ++ tailWord_5169742) baseStart_5169742 baseEnd_5169742 := by
    simpa [prefixWord, tailWord_5169742, baseEnd_5169742] using wordTrace_append hprefix tailTrace_5169742
  have hstable : (prefixWord ++ tailWord_5169742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169742).length < 2 ^ (prefixWord ++ tailWord_5169742).sum := by decide
  have hdescent : baseEnd_5169742 < baseStart_5169742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169756 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_5169756 : Nat := 118140960795 + 5169756 * 2 ^ 59
def prefixEnd_5169756 : Nat := 4983230072969 + 3 ^ 40 * 5169756 * 2
def baseEnd_5169756 : Nat := 2654569694465180539574731

theorem tailTrace_5169756 : CollatzResearch.WordTrace tailWord_5169756 prefixEnd_5169756 2654569694465180539574731 := by
  unfold tailWord_5169756
  simp only [CollatzResearch.WordTrace]
  refine ⟨94278245929432205438368561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125704327905909607251158081 94278245929432205438368561)
  ·
    refine ⟨70708684447074154078776421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94278245929432205438368561 70708684447074154078776421)
    ·
      refine ⟨13257878333826403889770579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70708684447074154078776421 13257878333826403889770579)
      ·
        refine ⟨19886817500739605834655869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13257878333826403889770579 19886817500739605834655869)
        ·
          refine ⟨7457556562777352187995951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19886817500739605834655869 7457556562777352187995951)
          ·
            refine ⟨11186334844166028281993927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457556562777352187995951 11186334844166028281993927)
            ·
              refine ⟨16779502266249042422990891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11186334844166028281993927 16779502266249042422990891)
              ·
                refine ⟨25169253399373563634486337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779502266249042422990891 25169253399373563634486337)
                ·
                  refine ⟨18876940049530172725864753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25169253399373563634486337 18876940049530172725864753)
                  ·
                    refine ⟨14157705037147629544398565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18876940049530172725864753 14157705037147629544398565)
                    ·
                      refine ⟨2654569694465180539574731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14157705037147629544398565 2654569694465180539574731)
                      ·
                        rfl

theorem cell23_5169756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_5169756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169756 prefixEnd_5169756 := by exact prefixLift 5169756
  have htrace : WordTrace (prefixWord ++ tailWord_5169756) baseStart_5169756 baseEnd_5169756 := by
    simpa [prefixWord, tailWord_5169756, baseEnd_5169756] using wordTrace_append hprefix tailTrace_5169756
  have hstable : (prefixWord ++ tailWord_5169756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169756).length < 2 ^ (prefixWord ++ tailWord_5169756).sum := by decide
  have hdescent : baseEnd_5169756 < baseStart_5169756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169769 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 5, 2]
def baseStart_5169769 : Nat := 118140960795 + 5169769 * 2 ^ 59
def prefixEnd_5169769 : Nat := 4983230072969 + 3 ^ 40 * 5169769 * 2
def baseEnd_5169769 : Nat := 2654576369713688988712171

theorem tailTrace_5169769 : CollatzResearch.WordTrace tailWord_5169769 prefixEnd_5169769 2654576369713688988712171 := by
  unfold tailWord_5169769
  simp only [CollatzResearch.WordTrace]
  refine ⟨188556966007817314096960361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125704644005211542731306907 188556966007817314096960361)
  ·
    refine ⟨141417724505862985572720271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188556966007817314096960361 141417724505862985572720271)
    ·
      refine ⟨212126586758794478359080407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141417724505862985572720271 212126586758794478359080407)
      ·
        refine ⟨318189880138191717538620611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212126586758794478359080407 318189880138191717538620611)
        ·
          refine ⟨477284820207287576307930917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318189880138191717538620611 477284820207287576307930917)
          ·
            refine ⟨89490903788866420557737047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 477284820207287576307930917 89490903788866420557737047)
            ·
              refine ⟨134236355683299630836605571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89490903788866420557737047 134236355683299630836605571)
              ·
                refine ⟨201354533524949446254908357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134236355683299630836605571 201354533524949446254908357)
                ·
                  refine ⟨37753975035928021172795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201354533524949446254908357 37753975035928021172795317)
                  ·
                    refine ⟨3539435159618251984949561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37753975035928021172795317 3539435159618251984949561)
                    ·
                      refine ⟨2654576369713688988712171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539435159618251984949561 2654576369713688988712171)
                      ·
                        rfl

theorem cell23_5169769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5, 2].length) (baseStart_5169769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169769 prefixEnd_5169769 := by exact prefixLift 5169769
  have htrace : WordTrace (prefixWord ++ tailWord_5169769) baseStart_5169769 baseEnd_5169769 := by
    simpa [prefixWord, tailWord_5169769, baseEnd_5169769] using wordTrace_append hprefix tailTrace_5169769
  have hstable : (prefixWord ++ tailWord_5169769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169769).length < 2 ^ (prefixWord ++ tailWord_5169769).sum := by decide
  have hdescent : baseEnd_5169769 < baseStart_5169769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169772 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_5169772 : Nat := 118140960795 + 5169772 * 2 ^ 59
def prefixEnd_5169772 : Nat := 4983230072969 + 3 ^ 40 * 5169772 * 2
def baseEnd_5169772 : Nat := 2654577910155652476974657

theorem tailTrace_5169772 : CollatzResearch.WordTrace tailWord_5169772 prefixEnd_5169772 2654577910155652476974657 := by
  unfold tailWord_5169772
  simp only [CollatzResearch.WordTrace]
  refine ⟨94278537713403222804659785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125704716951204297072879713 94278537713403222804659785)
  ·
    refine ⟨70708903285052417103494839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94278537713403222804659785 70708903285052417103494839)
    ·
      refine ⟨106063354927578625655242259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70708903285052417103494839 106063354927578625655242259)
      ·
        refine ⟨159095032391367938482863389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106063354927578625655242259 159095032391367938482863389)
        ·
          refine ⟨59660637146762976931073771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159095032391367938482863389 59660637146762976931073771)
          ·
            refine ⟨89490955720144465396610657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59660637146762976931073771 89490955720144465396610657)
            ·
              refine ⟨67118216790108349047457993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89490955720144465396610657 67118216790108349047457993)
              ·
                refine ⟨50338662592581261785593495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67118216790108349047457993 50338662592581261785593495)
                ·
                  refine ⟨75507993888871892678390243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50338662592581261785593495 75507993888871892678390243)
                  ·
                    refine ⟨113261990833307839017585365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75507993888871892678390243 113261990833307839017585365)
                    ·
                      refine ⟨2654577910155652476974657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113261990833307839017585365 2654577910155652476974657)
                      ·
                        rfl

theorem cell23_5169772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_5169772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169772 prefixEnd_5169772 := by exact prefixLift 5169772
  have htrace : WordTrace (prefixWord ++ tailWord_5169772) baseStart_5169772 baseEnd_5169772 := by
    simpa [prefixWord, tailWord_5169772, baseEnd_5169772] using wordTrace_append hprefix tailTrace_5169772
  have hstable : (prefixWord ++ tailWord_5169772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169772).length < 2 ^ (prefixWord ++ tailWord_5169772).sum := by decide
  have hdescent : baseEnd_5169772 < baseStart_5169772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169794 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5169794 : Nat := 118140960795 + 5169794 * 2 ^ 59
def prefixEnd_5169794 : Nat := 4983230072969 + 3 ^ 40 * 5169794 * 2
def baseEnd_5169794 : Nat := 2654589206730051390899557

theorem tailTrace_5169794 : CollatzResearch.WordTrace tailWord_5169794 prefixEnd_5169794 2654589206730051390899557 := by
  unfold tailWord_5169794
  simp only [CollatzResearch.WordTrace]
  refine ⟨47139469458181685841655109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125705251888484495577746957 47139469458181685841655109)
  ·
    refine ⟨8838650523409066095310333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47139469458181685841655109 8838650523409066095310333)
    ·
      refine ⟨3314493946278399785741375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8838650523409066095310333 3314493946278399785741375)
      ·
        refine ⟨4971740919417599678612063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314493946278399785741375 4971740919417599678612063)
        ·
          refine ⟨7457611379126399517918095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4971740919417599678612063 7457611379126399517918095)
          ·
            refine ⟨11186417068689599276877143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457611379126399517918095 11186417068689599276877143)
            ·
              refine ⟨16779625603034398915315715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11186417068689599276877143 16779625603034398915315715)
              ·
                refine ⟨25169438404551598372973573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16779625603034398915315715 25169438404551598372973573)
                ·
                  refine ⟨4719269700853424694932545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25169438404551598372973573 4719269700853424694932545)
                  ·
                    refine ⟨3539452275640068521199409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719269700853424694932545 3539452275640068521199409)
                    ·
                      refine ⟨2654589206730051390899557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539452275640068521199409 2654589206730051390899557)
                      ·
                        rfl

theorem cell23_5169794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5169794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169794 prefixEnd_5169794 := by exact prefixLift 5169794
  have htrace : WordTrace (prefixWord ++ tailWord_5169794) baseStart_5169794 baseEnd_5169794 := by
    simpa [prefixWord, tailWord_5169794, baseEnd_5169794] using wordTrace_append hprefix tailTrace_5169794
  have hstable : (prefixWord ++ tailWord_5169794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169794).length < 2 ^ (prefixWord ++ tailWord_5169794).sum := by decide
  have hdescent : baseEnd_5169794 < baseStart_5169794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169799 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_5169799 : Nat := 118140960795 + 5169799 * 2 ^ 59
def prefixEnd_5169799 : Nat := 4983230072969 + 3 ^ 40 * 5169799 * 2
def baseEnd_5169799 : Nat := 2654591774133323871337033

theorem tailTrace_5169799 : CollatzResearch.WordTrace tailWord_5169799 prefixEnd_5169799 2654591774133323871337033 := by
  unfold tailWord_5169799
  simp only [CollatzResearch.WordTrace]
  refine ⟨188558060197708629220552451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125705373465139086147034967 188558060197708629220552451)
  ·
    refine ⟨282837090296562943830828677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188558060197708629220552451 282837090296562943830828677)
    ·
      refine ⟨53031954430605551968280377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282837090296562943830828677 53031954430605551968280377)
      ·
        refine ⟨39773965822954163976210283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53031954430605551968280377 39773965822954163976210283)
        ·
          refine ⟨59660948734431245964315425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39773965822954163976210283 59660948734431245964315425)
          ·
            refine ⟨44745711550823434473236569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59660948734431245964315425 44745711550823434473236569)
            ·
              refine ⟨33559283663117575854927427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44745711550823434473236569 33559283663117575854927427)
              ·
                refine ⟨50338925494676363782391141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33559283663117575854927427 50338925494676363782391141)
                ·
                  refine ⟨9438548530251818209198339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50338925494676363782391141 9438548530251818209198339)
                  ·
                    refine ⟨14157822795377727313797509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9438548530251818209198339 14157822795377727313797509)
                    ·
                      refine ⟨2654591774133323871337033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14157822795377727313797509 2654591774133323871337033)
                      ·
                        rfl

theorem cell23_5169799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_5169799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169799 prefixEnd_5169799 := by exact prefixLift 5169799
  have htrace : WordTrace (prefixWord ++ tailWord_5169799) baseStart_5169799 baseEnd_5169799 := by
    simpa [prefixWord, tailWord_5169799, baseEnd_5169799] using wordTrace_append hprefix tailTrace_5169799
  have hstable : (prefixWord ++ tailWord_5169799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169799).length < 2 ^ (prefixWord ++ tailWord_5169799).sum := by decide
  have hdescent : baseEnd_5169799 < baseStart_5169799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169816 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5169816 : Nat := 118140960795 + 5169816 * 2 ^ 59
def prefixEnd_5169816 : Nat := 4983230072969 + 3 ^ 40 * 5169816 * 2
def baseEnd_5169816 : Nat := 2654600503304450304824455

theorem tailTrace_5169816 : CollatzResearch.WordTrace tailWord_5169816 prefixEnd_5169816 2654600503304450304824455 := by
  unfold tailWord_5169816
  simp only [CollatzResearch.WordTrace]
  refine ⟨94279340119323520561960651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125705786825764694082614201 94279340119323520561960651)
  ·
    refine ⟨141419010178985280842940977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94279340119323520561960651 141419010178985280842940977)
    ·
      refine ⟨106064257634238960632205733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141419010178985280842940977 106064257634238960632205733)
      ·
        refine ⟨19887048306419805118538575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106064257634238960632205733 19887048306419805118538575)
        ·
          refine ⟨29830572459629707677807863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19887048306419805118538575 29830572459629707677807863)
          ·
            refine ⟨44745858689444561516711795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29830572459629707677807863 44745858689444561516711795)
            ·
              refine ⟨67118788034166842275067693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44745858689444561516711795 67118788034166842275067693)
              ·
                refine ⟨25169545512812565853150385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67118788034166842275067693 25169545512812565853150385)
                ·
                  refine ⟨18877159134609424389862789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25169545512812565853150385 18877159134609424389862789)
                  ·
                    refine ⟨3539467337739267073099273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18877159134609424389862789 3539467337739267073099273)
                    ·
                      refine ⟨2654600503304450304824455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539467337739267073099273 2654600503304450304824455)
                      ·
                        rfl

theorem cell23_5169816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5169816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169816 prefixEnd_5169816 := by exact prefixLift 5169816
  have htrace : WordTrace (prefixWord ++ tailWord_5169816) baseStart_5169816 baseEnd_5169816 := by
    simpa [prefixWord, tailWord_5169816, baseEnd_5169816] using wordTrace_append hprefix tailTrace_5169816
  have hstable : (prefixWord ++ tailWord_5169816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169816).length < 2 ^ (prefixWord ++ tailWord_5169816).sum := by decide
  have hdescent : baseEnd_5169816 < baseStart_5169816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169843 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 1, 4]
def baseStart_5169843 : Nat := 118140960795 + 5169843 * 2 ^ 59
def prefixEnd_5169843 : Nat := 4983230072969 + 3 ^ 40 * 5169843 * 2
def baseEnd_5169843 : Nat := 884871455760707233062277

theorem tailTrace_5169843 : CollatzResearch.WordTrace tailWord_5169843 prefixEnd_5169843 884871455760707233062277 := by
  unfold tailWord_5169843
  simp only [CollatzResearch.WordTrace]
  refine ⟨188559665009549224735154183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125706443339699483156769455 188559665009549224735154183)
  ·
    refine ⟨282839497514323837102731275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188559665009549224735154183 282839497514323837102731275)
    ·
      refine ⟨424259246271485755654096913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282839497514323837102731275 424259246271485755654096913)
      ·
        refine ⟨318194434703614316740572685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424259246271485755654096913 318194434703614316740572685)
        ·
          refine ⟨119322913013855368777714757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318194434703614316740572685 119322913013855368777714757)
          ·
            refine ⟨22373046190097881645821517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119322913013855368777714757 22373046190097881645821517)
            ·
              refine ⟨8389892321286705617183069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22373046190097881645821517 8389892321286705617183069)
              ·
                refine ⟨3146209620482514606443651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8389892321286705617183069 3146209620482514606443651)
                ·
                  refine ⟨4719314430723771909665477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146209620482514606443651 4719314430723771909665477)
                  ·
                    refine ⟨884871455760707233062277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4719314430723771909665477 884871455760707233062277)
                    ·
                      rfl

theorem cell23_5169843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 4].length) (baseStart_5169843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169843 prefixEnd_5169843 := by exact prefixLift 5169843
  have htrace : WordTrace (prefixWord ++ tailWord_5169843) baseStart_5169843 baseEnd_5169843 := by
    simpa [prefixWord, tailWord_5169843, baseEnd_5169843] using wordTrace_append hprefix tailTrace_5169843
  have hstable : (prefixWord ++ tailWord_5169843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169843).length < 2 ^ (prefixWord ++ tailWord_5169843).sum := by decide
  have hdescent : baseEnd_5169843 < baseStart_5169843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169893 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_5169893 : Nat := 118140960795 + 5169893 * 2 ^ 59
def prefixEnd_5169893 : Nat := 4983230072969 + 3 ^ 40 * 5169893 * 2
def baseEnd_5169893 : Nat := 2654640041314846503561601

theorem tailTrace_5169893 : CollatzResearch.WordTrace tailWord_5169893 prefixEnd_5169893 2654640041314846503561601 := by
  unfold tailWord_5169893
  simp only [CollatzResearch.WordTrace]
  refine ⟨188561488659368083274474333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125707659106245388849649555 188561488659368083274474333)
  ·
    refine ⟨70710558247263031227927875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188561488659368083274474333 70710558247263031227927875)
    ·
      refine ⟨106065837370894546841891813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70710558247263031227927875 106065837370894546841891813)
      ·
        refine ⟨19887344507042727532854715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106065837370894546841891813 19887344507042727532854715)
        ·
          refine ⟨29831016760564091299282073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19887344507042727532854715 29831016760564091299282073)
          ·
            refine ⟨22373262570423068474461555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29831016760564091299282073 22373262570423068474461555)
            ·
              refine ⟨33559893855634602711692333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22373262570423068474461555 33559893855634602711692333)
              ·
                refine ⟨12584960195862976016884625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33559893855634602711692333 12584960195862976016884625)
                ·
                  refine ⟨9438720146897232012663469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12584960195862976016884625 9438720146897232012663469)
                  ·
                    refine ⟨3539520055086462004748801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9438720146897232012663469 3539520055086462004748801)
                    ·
                      refine ⟨2654640041314846503561601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539520055086462004748801 2654640041314846503561601)
                      ·
                        rfl

theorem cell23_5169893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_5169893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169893 prefixEnd_5169893 := by exact prefixLift 5169893
  have htrace : WordTrace (prefixWord ++ tailWord_5169893) baseStart_5169893 baseEnd_5169893 := by
    simpa [prefixWord, tailWord_5169893, baseEnd_5169893] using wordTrace_append hprefix tailTrace_5169893
  have hstable : (prefixWord ++ tailWord_5169893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169893).length < 2 ^ (prefixWord ++ tailWord_5169893).sum := by decide
  have hdescent : baseEnd_5169893 < baseStart_5169893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169903 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 1, 5]
def baseStart_5169903 : Nat := 118140960795 + 5169903 * 2 ^ 59
def prefixEnd_5169903 : Nat := 4983230072969 + 3 ^ 40 * 5169903 * 2
def baseEnd_5169903 : Nat := 884881725373797154812185

theorem tailTrace_5169903 : CollatzResearch.WordTrace tailWord_5169903 prefixEnd_5169903 884881725373797154812185 := by
  unfold tailWord_5169903
  simp only [CollatzResearch.WordTrace]
  refine ⟨188561853389331854982338363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125707902259554569988225575 188561853389331854982338363)
  ·
    refine ⟨282842780083997782473507545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188561853389331854982338363 282842780083997782473507545)
    ·
      refine ⟨212132085062998336855130659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282842780083997782473507545 212132085062998336855130659)
      ·
        refine ⟨318198127594497505282695989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212132085062998336855130659 318198127594497505282695989)
        ·
          refine ⟨29831074461984141120252749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318198127594497505282695989 29831074461984141120252749)
          ·
            refine ⟨11186652923244052920094781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29831074461984141120252749 11186652923244052920094781)
            ·
              refine ⟨4194994846216519845035543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11186652923244052920094781 4194994846216519845035543)
              ·
                refine ⟨6292492269324779767553315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4194994846216519845035543 6292492269324779767553315)
                ·
                  refine ⟨9438738403987169651329973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292492269324779767553315 9438738403987169651329973)
                  ·
                    refine ⟨884881725373797154812185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9438738403987169651329973 884881725373797154812185)
                    ·
                      rfl

theorem cell23_5169903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_5169903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169903 prefixEnd_5169903 := by exact prefixLift 5169903
  have htrace : WordTrace (prefixWord ++ tailWord_5169903) baseStart_5169903 baseEnd_5169903 := by
    simpa [prefixWord, tailWord_5169903, baseEnd_5169903] using wordTrace_append hprefix tailTrace_5169903
  have hstable : (prefixWord ++ tailWord_5169903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169903).length < 2 ^ (prefixWord ++ tailWord_5169903).sum := by decide
  have hdescent : baseEnd_5169903 < baseStart_5169903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169919 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_5169919 : Nat := 118140960795 + 5169919 * 2 ^ 59
def prefixEnd_5169919 : Nat := 4983230072969 + 3 ^ 40 * 5169919 * 2
def baseEnd_5169919 : Nat := 2654653391811863401836481

theorem tailTrace_5169919 : CollatzResearch.WordTrace tailWord_5169919 prefixEnd_5169919 2654653391811863401836481 := by
  unfold tailWord_5169919
  simp only [CollatzResearch.WordTrace]
  refine ⟨188562436957273889714920811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125708291304849259809947207 188562436957273889714920811)
  ·
    refine ⟨282843655435910834572381217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188562436957273889714920811 282843655435910834572381217)
    ·
      refine ⟨212132741576933125929285913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282843655435910834572381217 212132741576933125929285913)
      ·
        refine ⟨159099556182699844446964435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212132741576933125929285913 159099556182699844446964435)
        ·
          refine ⟨238649334274049766670446653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159099556182699844446964435 238649334274049766670446653)
          ·
            refine ⟨89493500352768662501417495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238649334274049766670446653 89493500352768662501417495)
            ·
              refine ⟨134240250529152993752126243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89493500352768662501417495 134240250529152993752126243)
              ·
                refine ⟨201360375793729490628189365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134240250529152993752126243 201360375793729490628189365)
                ·
                  refine ⟨18877535230662139746392753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201360375793729490628189365 18877535230662139746392753)
                  ·
                    refine ⟨14158151422996604809794565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18877535230662139746392753 14158151422996604809794565)
                    ·
                      refine ⟨2654653391811863401836481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14158151422996604809794565 2654653391811863401836481)
                      ·
                        rfl

theorem cell23_5169919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_5169919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169919 prefixEnd_5169919 := by exact prefixLift 5169919
  have htrace : WordTrace (prefixWord ++ tailWord_5169919) baseStart_5169919 baseEnd_5169919 := by
    simpa [prefixWord, tailWord_5169919, baseEnd_5169919] using wordTrace_append hprefix tailTrace_5169919
  have hstable : (prefixWord ++ tailWord_5169919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169919).length < 2 ^ (prefixWord ++ tailWord_5169919).sum := by decide
  have hdescent : baseEnd_5169919 < baseStart_5169919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169923 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 3, 2, 2]
def baseStart_5169923 : Nat := 118140960795 + 5169923 * 2 ^ 59
def prefixEnd_5169923 : Nat := 4983230072969 + 3 ^ 40 * 5169923 * 2
def baseEnd_5169923 : Nat := 2654655445734481386186463

theorem tailTrace_5169923 : CollatzResearch.WordTrace tailWord_5169923 prefixEnd_5169923 2654655445734481386186463 := by
  unfold tailWord_5169923
  simp only [CollatzResearch.WordTrace]
  refine ⟨188562582849259398398066423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125708388566172932265377615 188562582849259398398066423)
  ·
    refine ⟨282843874273889097597099635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188562582849259398398066423 282843874273889097597099635)
    ·
      refine ⟨424265811410833646395649453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282843874273889097597099635 424265811410833646395649453)
      ·
        refine ⟨159099679279062617398368545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424265811410833646395649453 159099679279062617398368545)
        ·
          refine ⟨119324759459296963048776409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159099679279062617398368545 119324759459296963048776409)
          ·
            refine ⟨89493569594472722286582307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119324759459296963048776409 89493569594472722286582307)
            ·
              refine ⟨134240354391709083429873461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89493569594472722286582307 134240354391709083429873461)
              ·
                refine ⟨12585033224222726571550637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134240354391709083429873461 12585033224222726571550637)
                ·
                  refine ⟨4719387459083522464331489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12585033224222726571550637 4719387459083522464331489)
                  ·
                    refine ⟨3539540594312641848248617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719387459083522464331489 3539540594312641848248617)
                    ·
                      refine ⟨2654655445734481386186463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539540594312641848248617 2654655445734481386186463)
                      ·
                        rfl

theorem cell23_5169923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_5169923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169923 prefixEnd_5169923 := by exact prefixLift 5169923
  have htrace : WordTrace (prefixWord ++ tailWord_5169923) baseStart_5169923 baseEnd_5169923 := by
    simpa [prefixWord, tailWord_5169923, baseEnd_5169923] using wordTrace_append hprefix tailTrace_5169923
  have hstable : (prefixWord ++ tailWord_5169923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169923).length < 2 ^ (prefixWord ++ tailWord_5169923).sum := by decide
  have hdescent : baseEnd_5169923 < baseStart_5169923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169929 : List Nat := [1, 2, 1, 1, 3, 2, 5, 8]
def baseStart_5169929 : Nat := 118140960795 + 5169929 * 2 ^ 59
def prefixEnd_5169929 : Nat := 4983230072969 + 3 ^ 40 * 5169929 * 2
def baseEnd_5169929 : Nat := 98320686171052161581905

theorem tailTrace_5169929 : CollatzResearch.WordTrace tailWord_5169929 prefixEnd_5169929 98320686171052161581905 := by
  unfold tailWord_5169929
  simp only [CollatzResearch.WordTrace]
  refine ⟨188562801687237661422784841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125708534458158440948523227 188562801687237661422784841)
  ·
    refine ⟨141422101265428246067088631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188562801687237661422784841 141422101265428246067088631)
    ·
      refine ⟨212133151898142369100632947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141422101265428246067088631 212133151898142369100632947)
      ·
        refine ⟨318199727847213553650949421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212133151898142369100632947 318199727847213553650949421)
        ·
          refine ⟨119324897942705082619106033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318199727847213553650949421 119324897942705082619106033)
          ·
            refine ⟨89493673457028811964329525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119324897942705082619106033 89493673457028811964329525)
            ·
              refine ⟨8390031886596451121655893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89493673457028811964329525 8390031886596451121655893)
              ·
                refine ⟨98320686171052161581905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8390031886596451121655893 98320686171052161581905)
                ·
                  rfl

theorem cell23_5169929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 8].length) (baseStart_5169929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169929 prefixEnd_5169929 := by exact prefixLift 5169929
  have htrace : WordTrace (prefixWord ++ tailWord_5169929) baseStart_5169929 baseEnd_5169929 := by
    simpa [prefixWord, tailWord_5169929, baseEnd_5169929] using wordTrace_append hprefix tailTrace_5169929
  have hstable : (prefixWord ++ tailWord_5169929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169929).length < 2 ^ (prefixWord ++ tailWord_5169929).sum := by decide
  have hdescent : baseEnd_5169929 < baseStart_5169929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169946 : List Nat := [3, 1, 1, 3, 2, 1, 5, 7]
def baseStart_5169946 : Nat := 118140960795 + 5169946 * 2 ^ 59
def prefixEnd_5169946 : Nat := 4983230072969 + 3 ^ 40 * 5169946 * 2
def baseEnd_5169946 : Nat := 98321009473686473933291

theorem tailTrace_5169946 : CollatzResearch.WordTrace tailWord_5169946 prefixEnd_5169946 98321009473686473933291 := by
  unfold tailWord_5169946
  simp only [CollatzResearch.WordTrace]
  refine ⟨47140855432044018331538423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125708947818784048884102461 47140855432044018331538423)
  ·
    refine ⟨70711283148066027497307635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47140855432044018331538423 70711283148066027497307635)
    ·
      refine ⟨106066924722099041245961453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70711283148066027497307635 106066924722099041245961453)
      ·
        refine ⟨39775096770787140467235545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106066924722099041245961453 39775096770787140467235545)
        ·
          refine ⟨29831322578090355350426659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39775096770787140467235545 29831322578090355350426659)
          ·
            refine ⟨44746983867135533025639989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29831322578090355350426659 44746983867135533025639989)
            ·
              refine ⟨4195029737543956221153749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44746983867135533025639989 4195029737543956221153749)
              ·
                refine ⟨98321009473686473933291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4195029737543956221153749 98321009473686473933291)
                ·
                  rfl

theorem cell23_5169946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_5169946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169946 prefixEnd_5169946 := by exact prefixLift 5169946
  have htrace : WordTrace (prefixWord ++ tailWord_5169946) baseStart_5169946 baseEnd_5169946 := by
    simpa [prefixWord, tailWord_5169946, baseEnd_5169946] using wordTrace_append hprefix tailTrace_5169946
  have hstable : (prefixWord ++ tailWord_5169946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169946).length < 2 ^ (prefixWord ++ tailWord_5169946).sum := by decide
  have hdescent : baseEnd_5169946 < baseStart_5169946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169957 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 1, 2, 2]
def baseStart_5169957 : Nat := 118140960795 + 5169957 * 2 ^ 59
def prefixEnd_5169957 : Nat := 4983230072969 + 3 ^ 40 * 5169957 * 2
def baseEnd_5169957 : Nat := 2654672904076734253161307

theorem tailTrace_5169957 : CollatzResearch.WordTrace tailWord_5169957 prefixEnd_5169957 2654672904076734253161307 := by
  unfold tailWord_5169957
  simp only [CollatzResearch.WordTrace]
  refine ⟨188563822931136222204804125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125709215287424148136536083 188563822931136222204804125)
  ·
    refine ⟨70711433599176083326801547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188563822931136222204804125 70711433599176083326801547)
    ·
      refine ⟨106067150398764124990202321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70711433599176083326801547 106067150398764124990202321)
      ·
        refine ⟨79550362799073093742651741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106067150398764124990202321 79550362799073093742651741)
        ·
          refine ⟨29831386049652410153494403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79550362799073093742651741 29831386049652410153494403)
          ·
            refine ⟨44747079074478615230241605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29831386049652410153494403 44747079074478615230241605)
            ·
              refine ⟨8390077326464740355670301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44747079074478615230241605 8390077326464740355670301)
              ·
                refine ⟨3146278997424277633376363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8390077326464740355670301 3146278997424277633376363)
                ·
                  refine ⟨4719418496136416450064545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146278997424277633376363 4719418496136416450064545)
                  ·
                    refine ⟨3539563872102312337548409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719418496136416450064545 3539563872102312337548409)
                    ·
                      refine ⟨2654672904076734253161307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539563872102312337548409 2654672904076734253161307)
                      ·
                        rfl

theorem cell23_5169957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_5169957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169957 prefixEnd_5169957 := by exact prefixLift 5169957
  have htrace : WordTrace (prefixWord ++ tailWord_5169957) baseStart_5169957 baseEnd_5169957 := by
    simpa [prefixWord, tailWord_5169957, baseEnd_5169957] using wordTrace_append hprefix tailTrace_5169957
  have hstable : (prefixWord ++ tailWord_5169957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169957).length < 2 ^ (prefixWord ++ tailWord_5169957).sum := by decide
  have hdescent : baseEnd_5169957 < baseStart_5169957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169974 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5169974 : Nat := 118140960795 + 5169974 * 2 ^ 59
def prefixEnd_5169974 : Nat := 4983230072969 + 3 ^ 40 * 5169974 * 2
def baseEnd_5169974 : Nat := 2654681633247860686648729

theorem tailTrace_5169974 : CollatzResearch.WordTrace tailWord_5169974 prefixEnd_5169974 2654681633247860686648729 := by
  unfold tailWord_5169974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785277685754664631760811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125709628648049756072115317 11785277685754664631760811)
  ·
    refine ⟨17677916528631996947641217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11785277685754664631760811 17677916528631996947641217)
    ·
      refine ⟨13258437396473997710730913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17677916528631996947641217 13258437396473997710730913)
      ·
        refine ⟨9943828047355498283048185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13258437396473997710730913 9943828047355498283048185)
        ·
          refine ⟨7457871035516623712286139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9943828047355498283048185 7457871035516623712286139)
          ·
            refine ⟨11186806553274935568429209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7457871035516623712286139 11186806553274935568429209)
            ·
              refine ⟨8390104914956201676321907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11186806553274935568429209 8390104914956201676321907)
              ·
                refine ⟨12585157372434302514482861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8390104914956201676321907 12585157372434302514482861)
                ·
                  refine ⟨4719434014662863442931073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12585157372434302514482861 4719434014662863442931073)
                  ·
                    refine ⟨3539575510997147582198305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719434014662863442931073 3539575510997147582198305)
                    ·
                      refine ⟨2654681633247860686648729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539575510997147582198305 2654681633247860686648729)
                      ·
                        rfl

theorem cell23_5169974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5169974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169974 prefixEnd_5169974 := by exact prefixLift 5169974
  have htrace : WordTrace (prefixWord ++ tailWord_5169974) baseStart_5169974 baseEnd_5169974 := by
    simpa [prefixWord, tailWord_5169974, baseEnd_5169974] using wordTrace_append hprefix tailTrace_5169974
  have hstable : (prefixWord ++ tailWord_5169974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169974).length < 2 ^ (prefixWord ++ tailWord_5169974).sum := by decide
  have hdescent : baseEnd_5169974 < baseStart_5169974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169989 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_5169989 : Nat := 118140960795 + 5169989 * 2 ^ 59
def prefixEnd_5169989 : Nat := 4983230072969 + 3 ^ 40 * 5169989 * 2
def baseEnd_5169989 : Nat := 884896445152559375987053

theorem tailTrace_5169989 : CollatzResearch.WordTrace tailWord_5169989 prefixEnd_5169989 884896445152559375987053 := by
  unfold tailWord_5169989
  simp only [CollatzResearch.WordTrace]
  refine ⟨188564990067020291669969021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125709993378013527779979347 188564990067020291669969021)
  ·
    refine ⟨70711871275132609376238383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188564990067020291669969021 70711871275132609376238383)
    ·
      refine ⟨106067806912698914064357575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70711871275132609376238383 106067806912698914064357575)
      ·
        refine ⟨159101710369048371096536363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106067806912698914064357575 159101710369048371096536363)
        ·
          refine ⟨238652565553572556644804545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159101710369048371096536363 238652565553572556644804545)
          ·
            refine ⟨178989424165179417483603409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238652565553572556644804545 178989424165179417483603409)
            ·
              refine ⟨134242068123884563112702557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178989424165179417483603409 134242068123884563112702557)
              ·
                refine ⟨50340775546456711167263459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134242068123884563112702557 50340775546456711167263459)
                ·
                  refine ⟨75511163319685066750895189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50340775546456711167263459 75511163319685066750895189)
                  ·
                    refine ⟨884896445152559375987053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75511163319685066750895189 884896445152559375987053)
                    ·
                      rfl

theorem cell23_5169989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_5169989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169989 prefixEnd_5169989 := by exact prefixLift 5169989
  have htrace : WordTrace (prefixWord ++ tailWord_5169989) baseStart_5169989 baseEnd_5169989 := by
    simpa [prefixWord, tailWord_5169989, baseEnd_5169989] using wordTrace_append hprefix tailTrace_5169989
  have hstable : (prefixWord ++ tailWord_5169989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169989).length < 2 ^ (prefixWord ++ tailWord_5169989).sum := by decide
  have hdescent : baseEnd_5169989 < baseStart_5169989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169997 : List Nat := [1, 6, 1, 2, 3, 1, 2, 7]
def baseStart_5169997 : Nat := 118140960795 + 5169997 * 2 ^ 59
def prefixEnd_5169997 : Nat := 4983230072969 + 3 ^ 40 * 5169997 * 2
def baseEnd_5169997 : Nat := 98321979381589410987449

theorem tailTrace_5169997 : CollatzResearch.WordTrace tailWord_5169997 prefixEnd_5169997 98321979381589410987449 := by
  unfold tailWord_5169997
  simp only [CollatzResearch.WordTrace]
  refine ⟨188565281850991309036260245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125710187900660872690840163 188565281850991309036260245)
  ·
    refine ⟨8838997586765217611074699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188565281850991309036260245 8838997586765217611074699)
    ·
      refine ⟨13258496380147826416612049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8838997586765217611074699 13258496380147826416612049)
      ·
        refine ⟨9943872285110869812459037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13258496380147826416612049 9943872285110869812459037)
        ·
          refine ⟨3728952106916576179672139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9943872285110869812459037 3728952106916576179672139)
          ·
            refine ⟨5593428160374864269508209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728952106916576179672139 5593428160374864269508209)
            ·
              refine ⟨4195071120281148202131157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5593428160374864269508209 4195071120281148202131157)
              ·
                refine ⟨98321979381589410987449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4195071120281148202131157 98321979381589410987449)
                ·
                  rfl

theorem cell23_5169997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 7].length) (baseStart_5169997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169997 prefixEnd_5169997 := by exact prefixLift 5169997
  have htrace : WordTrace (prefixWord ++ tailWord_5169997) baseStart_5169997 baseEnd_5169997 := by
    simpa [prefixWord, tailWord_5169997, baseEnd_5169997] using wordTrace_append hprefix tailTrace_5169997
  have hstable : (prefixWord ++ tailWord_5169997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169997).length < 2 ^ (prefixWord ++ tailWord_5169997).sum := by decide
  have hdescent : baseEnd_5169997 < baseStart_5169997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5169999 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_5169999 : Nat := 118140960795 + 5169999 * 2 ^ 59
def prefixEnd_5169999 : Nat := 4983230072969 + 3 ^ 40 * 5169999 * 2
def baseEnd_5169999 : Nat := 2654694470264223088836113

theorem tailTrace_5169999 : CollatzResearch.WordTrace tailWord_5169999 prefixEnd_5169999 2654694470264223088836113 := by
  unfold tailWord_5169999
  simp only [CollatzResearch.WordTrace]
  refine ⟨188565354796984063377833051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125710236531322708918555367 188565354796984063377833051)
  ·
    refine ⟨282848032195476095066749577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188565354796984063377833051 282848032195476095066749577)
    ·
      refine ⟨212136024146607071300062183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282848032195476095066749577 212136024146607071300062183)
      ·
        refine ⟨318204036219910606950093275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212136024146607071300062183 318204036219910606950093275)
        ·
          refine ⟨477306054329865910425139913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318204036219910606950093275 477306054329865910425139913)
          ·
            refine ⟨357979540747399432818854935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477306054329865910425139913 357979540747399432818854935)
            ·
              refine ⟨536969311121099149228282403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357979540747399432818854935 536969311121099149228282403)
              ·
                refine ⟨805453966681648723842423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536969311121099149228282403 805453966681648723842423605)
                ·
                  refine ⟨75511309376404567860227213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805453966681648723842423605 75511309376404567860227213)
                  ·
                    refine ⟨28316741016151712947585205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75511309376404567860227213 28316741016151712947585205)
                    ·
                      refine ⟨2654694470264223088836113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28316741016151712947585205 2654694470264223088836113)
                      ·
                        rfl

theorem cell23_5169999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_5169999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5169999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5169999 prefixEnd_5169999 := by exact prefixLift 5169999
  have htrace : WordTrace (prefixWord ++ tailWord_5169999) baseStart_5169999 baseEnd_5169999 := by
    simpa [prefixWord, tailWord_5169999, baseEnd_5169999] using wordTrace_append hprefix tailTrace_5169999
  have hstable : (prefixWord ++ tailWord_5169999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5169999).length < 2 ^ (prefixWord ++ tailWord_5169999).sum := by decide
  have hdescent : baseEnd_5169999 < baseStart_5169999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5169999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170016 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_5170016 : Nat := 118140960795 + 5170016 * 2 ^ 59
def prefixEnd_5170016 : Nat := 4983230072969 + 3 ^ 40 * 5170016 * 2
def baseEnd_5170016 : Nat := 2654703199435349522323535

theorem tailTrace_5170016 : CollatzResearch.WordTrace tailWord_5170016 prefixEnd_5170016 2654703199435349522323535 := by
  unfold tailWord_5170016
  simp only [CollatzResearch.WordTrace]
  refine ⟨94282987418961237640600951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125710649891948316854134601 94282987418961237640600951)
  ·
    refine ⟨141424481128441856460901427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94282987418961237640600951 141424481128441856460901427)
    ·
      refine ⟨212136721692662784691352141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141424481128441856460901427 212136721692662784691352141)
      ·
        refine ⟨79551270634748544259257053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212136721692662784691352141 79551270634748544259257053)
        ·
          refine ⟨29831726488030704097221395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79551270634748544259257053 29831726488030704097221395)
          ·
            refine ⟨44747589732046056145832093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29831726488030704097221395 44747589732046056145832093)
            ·
              refine ⟨16780346149517271054687035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44747589732046056145832093 16780346149517271054687035)
              ·
                refine ⟨25170519224275906582030553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16780346149517271054687035 25170519224275906582030553)
                ·
                  refine ⟨18877889418206929936522915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25170519224275906582030553 18877889418206929936522915)
                  ·
                    refine ⟨28316834127310394904784373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18877889418206929936522915 28316834127310394904784373)
                    ·
                      refine ⟨2654703199435349522323535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28316834127310394904784373 2654703199435349522323535)
                      ·
                        rfl

theorem cell23_5170016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_5170016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170016 prefixEnd_5170016 := by exact prefixLift 5170016
  have htrace : WordTrace (prefixWord ++ tailWord_5170016) baseStart_5170016 baseEnd_5170016 := by
    simpa [prefixWord, tailWord_5170016, baseEnd_5170016] using wordTrace_append hprefix tailTrace_5170016
  have hstable : (prefixWord ++ tailWord_5170016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170016).length < 2 ^ (prefixWord ++ tailWord_5170016).sum := by decide
  have hdescent : baseEnd_5170016 < baseStart_5170016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170047 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 2, 2, 2]
def baseStart_5170047 : Nat := 118140960795 + 5170047 * 2 ^ 59
def prefixEnd_5170047 : Nat := 4983230072969 + 3 ^ 40 * 5170047 * 2
def baseEnd_5170047 : Nat := 2654719117335638901035893

theorem tailTrace_5170047 : CollatzResearch.WordTrace tailWord_5170047 prefixEnd_5170047 2654719117335638901035893 := by
  unfold tailWord_5170047
  simp only [CollatzResearch.WordTrace]
  refine ⟨188567105500810167575580395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125711403667206778383720263 188567105500810167575580395)
  ·
    refine ⟨282850658251215251363370593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188567105500810167575580395 282850658251215251363370593)
    ·
      refine ⟨212137993688411438522527945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282850658251215251363370593 212137993688411438522527945)
      ·
        refine ⟨159103495266308578891895959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212137993688411438522527945 159103495266308578891895959)
        ·
          refine ⟨238655242899462868337843939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159103495266308578891895959 238655242899462868337843939)
          ·
            refine ⟨357982864349194302506765909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238655242899462868337843939 357982864349194302506765909)
            ·
              refine ⟨4195111691592120732501163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 357982864349194302506765909 4195111691592120732501163)
              ·
                refine ⟨6292667537388181098751745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195111691592120732501163 6292667537388181098751745)
                ·
                  refine ⟨4719500653041135824063809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6292667537388181098751745 4719500653041135824063809)
                  ·
                    refine ⟨3539625489780851868047857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719500653041135824063809 3539625489780851868047857)
                    ·
                      refine ⟨2654719117335638901035893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539625489780851868047857 2654719117335638901035893)
                      ·
                        rfl

theorem cell23_5170047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_5170047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170047 prefixEnd_5170047 := by exact prefixLift 5170047
  have htrace : WordTrace (prefixWord ++ tailWord_5170047) baseStart_5170047 baseEnd_5170047 := by
    simpa [prefixWord, tailWord_5170047, baseEnd_5170047] using wordTrace_append hprefix tailTrace_5170047
  have hstable : (prefixWord ++ tailWord_5170047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170047).length < 2 ^ (prefixWord ++ tailWord_5170047).sum := by decide
  have hdescent : baseEnd_5170047 < baseStart_5170047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170103 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_5170103 : Nat := 118140960795 + 5170103 * 2 ^ 59
def prefixEnd_5170103 : Nat := 4983230072969 + 3 ^ 40 * 5170103 * 2
def baseEnd_5170103 : Nat := 2654747872252290681935635

theorem tailTrace_5170103 : CollatzResearch.WordTrace tailWord_5170103 prefixEnd_5170103 2654747872252290681935635 := by
  unfold tailWord_5170103
  simp only [CollatzResearch.WordTrace]
  refine ⟨188569147988607289139618963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125712765325738192759745975 188569147988607289139618963)
  ·
    refine ⟨282853721982910933709428445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188569147988607289139618963 282853721982910933709428445)
    ·
      refine ⟨106070145743591600141035667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282853721982910933709428445 106070145743591600141035667)
      ·
        refine ⟨159105218615387400211553501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106070145743591600141035667 159105218615387400211553501)
        ·
          refine ⟨59664456980770275079332563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159105218615387400211553501 59664456980770275079332563)
          ·
            refine ⟨89496685471155412618998845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59664456980770275079332563 89496685471155412618998845)
            ·
              refine ⟨33561257051683279732124567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89496685471155412618998845 33561257051683279732124567)
              ·
                refine ⟨50341885577524919598186851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33561257051683279732124567 50341885577524919598186851)
                ·
                  refine ⟨75512828366287379397280277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50341885577524919598186851 75512828366287379397280277)
                  ·
                    refine ⟨3539663829669720909247513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75512828366287379397280277 3539663829669720909247513)
                    ·
                      refine ⟨2654747872252290681935635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539663829669720909247513 2654747872252290681935635)
                      ·
                        rfl

theorem cell23_5170103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_5170103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170103 prefixEnd_5170103 := by exact prefixLift 5170103
  have htrace : WordTrace (prefixWord ++ tailWord_5170103) baseStart_5170103 baseEnd_5170103 := by
    simpa [prefixWord, tailWord_5170103, baseEnd_5170103] using wordTrace_append hprefix tailTrace_5170103
  have hstable : (prefixWord ++ tailWord_5170103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170103).length < 2 ^ (prefixWord ++ tailWord_5170103).sum := by decide
  have hdescent : baseEnd_5170103 < baseStart_5170103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170123 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3]
def baseStart_5170123 : Nat := 118140960795 + 5170123 * 2 ^ 59
def prefixEnd_5170123 : Nat := 4983230072969 + 3 ^ 40 * 5170123 * 2
def baseEnd_5170123 : Nat := 2654758141865380603685543

theorem tailTrace_5170123 : CollatzResearch.WordTrace tailWord_5170123 prefixEnd_5170123 2654758141865380603685543 := by
  unfold tailWord_5170123
  simp only [CollatzResearch.WordTrace]
  refine ⟨188569877448534832555347023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125713251632356555036898015 188569877448534832555347023)
  ·
    refine ⟨282854816172802248833020535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188569877448534832555347023 282854816172802248833020535)
    ·
      refine ⟨424282224259203373249530803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282854816172802248833020535 424282224259203373249530803)
      ·
        refine ⟨636423336388805059874296205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424282224259203373249530803 636423336388805059874296205)
        ·
          refine ⟨238658751145801897452861077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636423336388805059874296205 238658751145801897452861077)
          ·
            refine ⟨11187128959959463943102863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238658751145801897452861077 11187128959959463943102863)
            ·
              refine ⟨16780693439939195914654295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11187128959959463943102863 16780693439939195914654295)
              ·
                refine ⟨25171040159908793871981443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16780693439939195914654295 25171040159908793871981443)
                ·
                  refine ⟨37756560239863190807972165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25171040159908793871981443 37756560239863190807972165)
                  ·
                    refine ⟨7079355044974348276494781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37756560239863190807972165 7079355044974348276494781)
                    ·
                      refine ⟨2654758141865380603685543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7079355044974348276494781 2654758141865380603685543)
                      ·
                        rfl

theorem cell23_5170123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 3].length) (baseStart_5170123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170123 prefixEnd_5170123 := by exact prefixLift 5170123
  have htrace : WordTrace (prefixWord ++ tailWord_5170123) baseStart_5170123 baseEnd_5170123 := by
    simpa [prefixWord, tailWord_5170123, baseEnd_5170123] using wordTrace_append hprefix tailTrace_5170123
  have hstable : (prefixWord ++ tailWord_5170123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170123).length < 2 ^ (prefixWord ++ tailWord_5170123).sum := by decide
  have hdescent : baseEnd_5170123 < baseStart_5170123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170143 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 8]
def baseStart_5170143 : Nat := 118140960795 + 5170143 * 2 ^ 59
def prefixEnd_5170143 : Nat := 4983230072969 + 3 ^ 40 * 5170143 * 2
def baseEnd_5170143 : Nat := 294974267942052280603939

theorem tailTrace_5170143 : CollatzResearch.WordTrace tailWord_5170143 prefixEnd_5170143 294974267942052280603939 := by
  unfold tailWord_5170143
  simp only [CollatzResearch.WordTrace]
  refine ⟨188570606908462375971075083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125713737938974917314050055 188570606908462375971075083)
  ·
    refine ⟨282855910362693563956612625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188570606908462375971075083 282855910362693563956612625)
    ·
      refine ⟨212141932772020172967459469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282855910362693563956612625 212141932772020172967459469)
      ·
        refine ⟨79553224789507564862797301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212141932772020172967459469 79553224789507564862797301)
        ·
          refine ⟨7458114824016334205887247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79553224789507564862797301 7458114824016334205887247)
          ·
            refine ⟨11187172236024501308830871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458114824016334205887247 11187172236024501308830871)
            ·
              refine ⟨16780758354036751963246307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11187172236024501308830871 16780758354036751963246307)
              ·
                refine ⟨25171137531055127944869461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16780758354036751963246307 25171137531055127944869461)
                ·
                  refine ⟨294974267942052280603939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25171137531055127944869461 294974267942052280603939)
                  ·
                    rfl

theorem cell23_5170143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 8].length) (baseStart_5170143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170143 prefixEnd_5170143 := by exact prefixLift 5170143
  have htrace : WordTrace (prefixWord ++ tailWord_5170143) baseStart_5170143 baseEnd_5170143 := by
    simpa [prefixWord, tailWord_5170143, baseEnd_5170143] using wordTrace_append hprefix tailTrace_5170143
  have hstable : (prefixWord ++ tailWord_5170143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170143).length < 2 ^ (prefixWord ++ tailWord_5170143).sum := by decide
  have hdescent : baseEnd_5170143 < baseStart_5170143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170190 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_5170190 : Nat := 118140960795 + 5170190 * 2 ^ 59
def prefixEnd_5170190 : Nat := 4983230072969 + 3 ^ 40 * 5170190 * 2
def baseEnd_5170190 : Nat := 884930848356410613849245

theorem tailTrace_5170190 : CollatzResearch.WordTrace tailWord_5170190 prefixEnd_5170190 884930848356410613849245 := by
  unfold tailWord_5170190
  simp only [CollatzResearch.WordTrace]
  refine ⟨23571540142411512874754503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125714880759528068665357349 23571540142411512874754503)
  ·
    refine ⟨35357310213617269312131755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23571540142411512874754503 35357310213617269312131755)
    ·
      refine ⟨53035965320425903968197633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35357310213617269312131755 53035965320425903968197633)
      ·
        refine ⟨39776973990319427976148225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53035965320425903968197633 39776973990319427976148225)
        ·
          refine ⟨29832730492739570982111169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39776973990319427976148225 29832730492739570982111169)
          ·
            refine ⟨22374547869554678236583377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29832730492739570982111169 22374547869554678236583377)
            ·
              refine ⟨16780910902166008677437533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22374547869554678236583377 16780910902166008677437533)
              ·
                refine ⟨6292841588312253254039075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16780910902166008677437533 6292841588312253254039075)
                ·
                  refine ⟨9439262382468379881058613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292841588312253254039075 9439262382468379881058613)
                  ·
                    refine ⟨884930848356410613849245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9439262382468379881058613 884930848356410613849245)
                    ·
                      rfl

theorem cell23_5170190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_5170190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170190 prefixEnd_5170190 := by exact prefixLift 5170190
  have htrace : WordTrace (prefixWord ++ tailWord_5170190) baseStart_5170190 baseEnd_5170190 := by
    simpa [prefixWord, tailWord_5170190, baseEnd_5170190] using wordTrace_append hprefix tailTrace_5170190
  have hstable : (prefixWord ++ tailWord_5170190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170190).length < 2 ^ (prefixWord ++ tailWord_5170190).sum := by decide
  have hdescent : baseEnd_5170190 < baseStart_5170190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170197 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_5170197 : Nat := 118140960795 + 5170197 * 2 ^ 59
def prefixEnd_5170197 : Nat := 4983230072969 + 3 ^ 40 * 5170197 * 2
def baseEnd_5170197 : Nat := 2654796139433813314160203

theorem tailTrace_5170197 : CollatzResearch.WordTrace tailWord_5170197 prefixEnd_5170197 2654796139433813314160203 := by
  unfold tailWord_5170197
  simp only [CollatzResearch.WordTrace]
  refine ⟨188572576450266743193540845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125715050966844495462360563 188572576450266743193540845)
  ·
    refine ⟨70714716168850028697577817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188572576450266743193540845 70714716168850028697577817)
    ·
      refine ⟨53036037126637521523183363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70714716168850028697577817 53036037126637521523183363)
      ·
        refine ⟨79554055689956282284775045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53036037126637521523183363 79554055689956282284775045)
        ·
          refine ⟨14916385441866802928395321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79554055689956282284775045 14916385441866802928395321)
          ·
            refine ⟨11187289081400102196296491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14916385441866802928395321 11187289081400102196296491)
            ·
              refine ⟨16780933622100153294444737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11187289081400102196296491 16780933622100153294444737)
              ·
                refine ⟨12585700216575114970833553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16780933622100153294444737 12585700216575114970833553)
                ·
                  refine ⟨9439275162431336228125165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12585700216575114970833553 9439275162431336228125165)
                  ·
                    refine ⟨3539728185911751085546937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9439275162431336228125165 3539728185911751085546937)
                    ·
                      refine ⟨2654796139433813314160203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539728185911751085546937 2654796139433813314160203)
                      ·
                        rfl

theorem cell23_5170197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_5170197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170197 prefixEnd_5170197 := by exact prefixLift 5170197
  have htrace : WordTrace (prefixWord ++ tailWord_5170197) baseStart_5170197 baseEnd_5170197 := by
    simpa [prefixWord, tailWord_5170197, baseEnd_5170197] using wordTrace_append hprefix tailTrace_5170197
  have hstable : (prefixWord ++ tailWord_5170197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170197).length < 2 ^ (prefixWord ++ tailWord_5170197).sum := by decide
  have hdescent : baseEnd_5170197 < baseStart_5170197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170204 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_5170204 : Nat := 118140960795 + 5170204 * 2 ^ 59
def prefixEnd_5170204 : Nat := 4983230072969 + 3 ^ 40 * 5170204 * 2
def baseEnd_5170204 : Nat := 2654799733798394786772671

theorem tailTrace_5170204 : CollatzResearch.WordTrace tailWord_5170204 prefixEnd_5170204 2654799733798394786772671 := by
  unfold tailWord_5170204
  simp only [CollatzResearch.WordTrace]
  refine ⟨94286415880620691694522833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125715221174160922259363777 94286415880620691694522833)
  ·
    refine ⟨70714811910465518770892125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94286415880620691694522833 70714811910465518770892125)
    ·
      refine ⟨26518054466424569539084547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70714811910465518770892125 26518054466424569539084547)
      ·
        refine ⟨39777081699636854308626821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26518054466424569539084547 39777081699636854308626821)
        ·
          refine ⟨7458202818681910182867529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39777081699636854308626821 7458202818681910182867529)
          ·
            refine ⟨5593652114011432637150647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7458202818681910182867529 5593652114011432637150647)
            ·
              refine ⟨8390478171017148955725971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593652114011432637150647 8390478171017148955725971)
              ·
                refine ⟨12585717256525723433588957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8390478171017148955725971 12585717256525723433588957)
                ·
                  refine ⟨4719643971197146287595859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12585717256525723433588957 4719643971197146287595859)
                  ·
                    refine ⟨7079465956795719431393789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4719643971197146287595859 7079465956795719431393789)
                    ·
                      refine ⟨2654799733798394786772671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7079465956795719431393789 2654799733798394786772671)
                      ·
                        rfl

theorem cell23_5170204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_5170204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170204 prefixEnd_5170204 := by exact prefixLift 5170204
  have htrace : WordTrace (prefixWord ++ tailWord_5170204) baseStart_5170204 baseEnd_5170204 := by
    simpa [prefixWord, tailWord_5170204, baseEnd_5170204] using wordTrace_append hprefix tailTrace_5170204
  have hstable : (prefixWord ++ tailWord_5170204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170204).length < 2 ^ (prefixWord ++ tailWord_5170204).sum := by decide
  have hdescent : baseEnd_5170204 < baseStart_5170204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170213 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_5170213 : Nat := 118140960795 + 5170213 * 2 ^ 59
def prefixEnd_5170213 : Nat := 4983230072969 + 3 ^ 40 * 5170213 * 2
def baseEnd_5170213 : Nat := 2654804355124285251560129

theorem tailTrace_5170213 : CollatzResearch.WordTrace tailWord_5170213 prefixEnd_5170213 2654804355124285251560129 := by
  unfold tailWord_5170213
  simp only [CollatzResearch.WordTrace]
  refine ⟨188573160018208777926123293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125715440012139185284082195 188573160018208777926123293)
  ·
    refine ⟨70714935006828291722296235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188573160018208777926123293 70714935006828291722296235)
    ·
      refine ⟨106072402510242437583444353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70714935006828291722296235 106072402510242437583444353)
      ·
        refine ⟨79554301882681828187583265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106072402510242437583444353 79554301882681828187583265)
        ·
          refine ⟨59665726412011371140687449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79554301882681828187583265 59665726412011371140687449)
          ·
            refine ⟨44749294809008528355515587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59665726412011371140687449 44749294809008528355515587)
            ·
              refine ⟨67123942213512792533273381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44749294809008528355515587 67123942213512792533273381)
              ·
                refine ⟨12585739165033648599988759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67123942213512792533273381 12585739165033648599988759)
                ·
                  refine ⟨18878608747550472899983139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12585739165033648599988759 18878608747550472899983139)
                  ·
                    refine ⟨28317913121325709349974709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18878608747550472899983139 28317913121325709349974709)
                    ·
                      refine ⟨2654804355124285251560129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28317913121325709349974709 2654804355124285251560129)
                      ·
                        rfl

theorem cell23_5170213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_5170213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170213 prefixEnd_5170213 := by exact prefixLift 5170213
  have htrace : WordTrace (prefixWord ++ tailWord_5170213) baseStart_5170213 baseEnd_5170213 := by
    simpa [prefixWord, tailWord_5170213, baseEnd_5170213] using wordTrace_append hprefix tailTrace_5170213
  have hstable : (prefixWord ++ tailWord_5170213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170213).length < 2 ^ (prefixWord ++ tailWord_5170213).sum := by decide
  have hdescent : baseEnd_5170213 < baseStart_5170213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170220 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_5170220 : Nat := 118140960795 + 5170220 * 2 ^ 59
def prefixEnd_5170220 : Nat := 4983230072969 + 3 ^ 40 * 5170220 * 2
def baseEnd_5170220 : Nat := 884935983162955574724199

theorem tailTrace_5170220 : CollatzResearch.WordTrace tailWord_5170220 prefixEnd_5170220 884935983162955574724199 := by
  unfold tailWord_5170220
  simp only [CollatzResearch.WordTrace]
  refine ⟨94286707664591709060814057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125715610219455612081085409 94286707664591709060814057)
  ·
    refine ⟨70715030748443781795610543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94286707664591709060814057 70715030748443781795610543)
    ·
      refine ⟨106072546122665672693415815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70715030748443781795610543 106072546122665672693415815)
      ·
        refine ⟨159108819183998509040123723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106072546122665672693415815 159108819183998509040123723)
        ·
          refine ⟨238663228775997763560185585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159108819183998509040123723 238663228775997763560185585)
          ·
            refine ⟨178997421581998322670139189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238663228775997763560185585 178997421581998322670139189)
            ·
              refine ⟨16781008273312342750325549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178997421581998322670139189 16781008273312342750325549)
              ·
                refine ⟨6292878102492128531372081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16781008273312342750325549 6292878102492128531372081)
                ·
                  refine ⟨4719658576869096398529061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6292878102492128531372081 4719658576869096398529061)
                  ·
                    refine ⟨884935983162955574724199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4719658576869096398529061 884935983162955574724199)
                    ·
                      rfl

theorem cell23_5170220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_5170220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170220 prefixEnd_5170220 := by exact prefixLift 5170220
  have htrace : WordTrace (prefixWord ++ tailWord_5170220) baseStart_5170220 baseEnd_5170220 := by
    simpa [prefixWord, tailWord_5170220, baseEnd_5170220] using wordTrace_append hprefix tailTrace_5170220
  have hstable : (prefixWord ++ tailWord_5170220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170220).length < 2 ^ (prefixWord ++ tailWord_5170220).sum := by decide
  have hdescent : baseEnd_5170220 < baseStart_5170220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170233 : List Nat := [1, 2, 1, 5, 2, 1, 2, 9]
def baseStart_5170233 : Nat := 118140960795 + 5170233 * 2 ^ 59
def prefixEnd_5170233 : Nat := 4983230072969 + 3 ^ 40 * 5170233 * 2
def baseEnd_5170233 : Nat := 98326467582865747159631

theorem tailTrace_5170233 : CollatzResearch.WordTrace tailWord_5170233 prefixEnd_5170233 98326467582865747159631 := by
  unfold tailWord_5170233
  simp only [CollatzResearch.WordTrace]
  refine ⟨188573889478136321341851353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125715926318757547561234235 188573889478136321341851353)
  ·
    refine ⟨141430417108602241006388515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188573889478136321341851353 141430417108602241006388515)
    ·
      refine ⟨212145625662903361509582773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141430417108602241006388515 212145625662903361509582773)
      ·
        refine ⟨19888652405897190141523385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212145625662903361509582773 19888652405897190141523385)
        ·
          refine ⟨14916489304422892606142539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19888652405897190141523385 14916489304422892606142539)
          ·
            refine ⟨22374733956634338909213809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14916489304422892606142539 22374733956634338909213809)
            ·
              refine ⟨16781050467475754181910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22374733956634338909213809 16781050467475754181910357)
              ·
                refine ⟨98326467582865747159631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16781050467475754181910357 98326467582865747159631)
                ·
                  rfl

theorem cell23_5170233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 9].length) (baseStart_5170233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170233 prefixEnd_5170233 := by exact prefixLift 5170233
  have htrace : WordTrace (prefixWord ++ tailWord_5170233) baseStart_5170233 baseEnd_5170233 := by
    simpa [prefixWord, tailWord_5170233, baseEnd_5170233] using wordTrace_append hprefix tailTrace_5170233
  have hstable : (prefixWord ++ tailWord_5170233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170233).length < 2 ^ (prefixWord ++ tailWord_5170233).sum := by decide
  have hdescent : baseEnd_5170233 < baseStart_5170233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170277 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_5170277 : Nat := 118140960795 + 5170277 * 2 ^ 59
def prefixEnd_5170277 : Nat := 4983230072969 + 3 ^ 40 * 5170277 * 2
def baseEnd_5170277 : Nat := 2654837217886173001159835

theorem tailTrace_5170277 : CollatzResearch.WordTrace tailWord_5170277 prefixEnd_5170277 2654837217886173001159835 := by
  unfold tailWord_5170277
  simp only [CollatzResearch.WordTrace]
  refine ⟨188575494289976916856453085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125716996193317944570968723 188575494289976916856453085)
  ·
    refine ⟨70715810358741343821169907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188575494289976916856453085 70715810358741343821169907)
    ·
      refine ⟨106073715538112015731754861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70715810358741343821169907 106073715538112015731754861)
      ·
        refine ⟨39777643326792005899408073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106073715538112015731754861 39777643326792005899408073)
        ·
          refine ⟨29833232495094004424556055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39777643326792005899408073 29833232495094004424556055)
          ·
            refine ⟨44749848742641006636834083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29833232495094004424556055 44749848742641006636834083)
            ·
              refine ⟨67124773113961509955251125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44749848742641006636834083 67124773113961509955251125)
              ·
                refine ⟨6292947479433891558304793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67124773113961509955251125 6292947479433891558304793)
                ·
                  refine ⟨4719710609575418668728595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6292947479433891558304793 4719710609575418668728595)
                  ·
                    refine ⟨7079565914363128003092893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4719710609575418668728595 7079565914363128003092893)
                    ·
                      refine ⟨2654837217886173001159835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7079565914363128003092893 2654837217886173001159835)
                      ·
                        rfl

theorem cell23_5170277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_5170277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170277 prefixEnd_5170277 := by exact prefixLift 5170277
  have htrace : WordTrace (prefixWord ++ tailWord_5170277) baseStart_5170277 baseEnd_5170277 := by
    simpa [prefixWord, tailWord_5170277, baseEnd_5170277] using wordTrace_append hprefix tailTrace_5170277
  have hstable : (prefixWord ++ tailWord_5170277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170277).length < 2 ^ (prefixWord ++ tailWord_5170277).sum := by decide
  have hdescent : baseEnd_5170277 < baseStart_5170277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170287 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 1, 3, 2]
def baseStart_5170287 : Nat := 118140960795 + 5170287 * 2 ^ 59
def prefixEnd_5170287 : Nat := 4983230072969 + 3 ^ 40 * 5170287 * 2
def baseEnd_5170287 : Nat := 2654842352692717962034789

theorem tailTrace_5170287 : CollatzResearch.WordTrace tailWord_5170287 prefixEnd_5170287 2654842352692717962034789 := by
  unfold tailWord_5170287
  simp only [CollatzResearch.WordTrace]
  refine ⟨188575859019940688564317115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125717239346627125709544743 188575859019940688564317115)
  ·
    refine ⟨282863788529911032846475673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188575859019940688564317115 282863788529911032846475673)
    ·
      refine ⟨212147841397433274634856755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282863788529911032846475673 212147841397433274634856755)
      ·
        refine ⟨318221762096149911952285133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212147841397433274634856755 318221762096149911952285133)
        ·
          refine ⟨119333160786056216982106925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318221762096149911952285133 119333160786056216982106925)
          ·
            refine ⟨44749935294771081368290097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119333160786056216982106925 44749935294771081368290097)
            ·
              refine ⟨33562451471078311026217573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44749935294771081368290097 33562451471078311026217573)
              ·
                refine ⟨6292959650827183317415795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33562451471078311026217573 6292959650827183317415795)
                ·
                  refine ⟨9439439476240774976123693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292959650827183317415795 9439439476240774976123693)
                  ·
                    refine ⟨3539789803590290616046385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9439439476240774976123693 3539789803590290616046385)
                    ·
                      refine ⟨2654842352692717962034789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539789803590290616046385 2654842352692717962034789)
                      ·
                        rfl

theorem cell23_5170287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3, 2].length) (baseStart_5170287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170287 prefixEnd_5170287 := by exact prefixLift 5170287
  have htrace : WordTrace (prefixWord ++ tailWord_5170287) baseStart_5170287 baseEnd_5170287 := by
    simpa [prefixWord, tailWord_5170287, baseEnd_5170287] using wordTrace_append hprefix tailTrace_5170287
  have hstable : (prefixWord ++ tailWord_5170287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170287).length < 2 ^ (prefixWord ++ tailWord_5170287).sum := by decide
  have hdescent : baseEnd_5170287 < baseStart_5170287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170304 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2]
def baseStart_5170304 : Nat := 118140960795 + 5170304 * 2 ^ 59
def prefixEnd_5170304 : Nat := 4983230072969 + 3 ^ 40 * 5170304 * 2
def baseEnd_5170304 : Nat := 2654851081863844395522211

theorem tailTrace_5170304 : CollatzResearch.WordTrace tailWord_5170304 prefixEnd_5170304 2654851081863844395522211 := by
  unfold tailWord_5170304
  simp only [CollatzResearch.WordTrace]
  refine ⟨94288239530439550233842983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125717652707252733645123977 94288239530439550233842983)
  ·
    refine ⟨141432359295659325350764475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94288239530439550233842983 141432359295659325350764475)
    ·
      refine ⟨212148538943488988026146713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141432359295659325350764475 212148538943488988026146713)
      ·
        refine ⟨159111404207616741019610035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212148538943488988026146713 159111404207616741019610035)
        ·
          refine ⟨238667106311425111529415053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159111404207616741019610035 238667106311425111529415053)
          ·
            refine ⟨89500164866784416823530645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238667106311425111529415053 89500164866784416823530645)
            ·
              refine ⟨4195320228130519538602999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89500164866784416823530645 4195320228130519538602999)
              ·
                refine ⟨6292980342195779307904499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195320228130519538602999 6292980342195779307904499)
                ·
                  refine ⟨9439470513293668961856749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6292980342195779307904499 9439470513293668961856749)
                  ·
                    refine ⟨3539801442485125860696281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9439470513293668961856749 3539801442485125860696281)
                    ·
                      refine ⟨2654851081863844395522211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3539801442485125860696281 2654851081863844395522211)
                      ·
                        rfl

theorem cell23_5170304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_5170304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170304 prefixEnd_5170304 := by exact prefixLift 5170304
  have htrace : WordTrace (prefixWord ++ tailWord_5170304) baseStart_5170304 baseEnd_5170304 := by
    simpa [prefixWord, tailWord_5170304, baseEnd_5170304] using wordTrace_append hprefix tailTrace_5170304
  have hstable : (prefixWord ++ tailWord_5170304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170304).length < 2 ^ (prefixWord ++ tailWord_5170304).sum := by decide
  have hdescent : baseEnd_5170304 < baseStart_5170304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170323 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 7]
def baseStart_5170323 : Nat := 118140960795 + 5170323 * 2 ^ 59
def prefixEnd_5170323 : Nat := 4983230072969 + 3 ^ 40 * 5170323 * 2
def baseEnd_5170323 : Nat := 294984537555142202353847

theorem tailTrace_5170323 : CollatzResearch.WordTrace tailWord_5170323 prefixEnd_5170323 294984537555142202353847 := by
  unfold tailWord_5170323
  simp only [CollatzResearch.WordTrace]
  refine ⟨188577172047810266712627623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125718114698540177808418415 188577172047810266712627623)
  ·
    refine ⟨282865758071715400068941435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188577172047810266712627623 282865758071715400068941435)
    ·
      refine ⟨424298637107573100103412153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282865758071715400068941435 424298637107573100103412153)
      ·
        refine ⟨318223977830679825077559115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424298637107573100103412153 318223977830679825077559115)
        ·
          refine ⟨477335966746019737616338673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318223977830679825077559115 477335966746019737616338673)
          ·
            refine ⟨358001975059514803212254005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477335966746019737616338673 358001975059514803212254005)
            ·
              refine ⟨33562685161829512801148813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 358001975059514803212254005 33562685161829512801148813)
              ·
                refine ⟨12586006935686067300430805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33562685161829512801148813 12586006935686067300430805)
                ·
                  refine ⟨294984537555142202353847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12586006935686067300430805 294984537555142202353847)
                  ·
                    rfl

theorem cell23_5170323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 7].length) (baseStart_5170323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170323 prefixEnd_5170323 := by exact prefixLift 5170323
  have htrace : WordTrace (prefixWord ++ tailWord_5170323) baseStart_5170323 baseEnd_5170323 := by
    simpa [prefixWord, tailWord_5170323, baseEnd_5170323] using wordTrace_append hprefix tailTrace_5170323
  have hstable : (prefixWord ++ tailWord_5170323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170323).length < 2 ^ (prefixWord ++ tailWord_5170323).sum := by decide
  have hdescent : baseEnd_5170323 < baseStart_5170323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170340 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 7]
def baseStart_5170340 : Nat := 118140960795 + 5170340 * 2 ^ 59
def prefixEnd_5170340 : Nat := 4983230072969 + 3 ^ 40 * 5170340 * 2
def baseEnd_5170340 : Nat := 294985507463045139408005

theorem tailTrace_5170340 : CollatzResearch.WordTrace tailWord_5170340 prefixEnd_5170340 294985507463045139408005 := by
  unfold tailWord_5170340
  simp only [CollatzResearch.WordTrace]
  refine ⟨94288896044374339307998237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125718528059165785743997649 94288896044374339307998237)
  ·
    refine ⟨35358336016640377240499339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94288896044374339307998237 35358336016640377240499339)
    ·
      refine ⟨53037504024960565860749009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35358336016640377240499339 53037504024960565860749009)
      ·
        refine ⟨39778128018720424395561757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53037504024960565860749009 39778128018720424395561757)
        ·
          refine ⟨14916798007020159148335659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39778128018720424395561757 14916798007020159148335659)
          ·
            refine ⟨22375197010530238722503489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14916798007020159148335659 22375197010530238722503489)
            ·
              refine ⟨16781397757897679041877617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22375197010530238722503489 16781397757897679041877617)
              ·
                refine ⟨12586048318423259281408213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16781397757897679041877617 12586048318423259281408213)
                ·
                  refine ⟨294985507463045139408005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12586048318423259281408213 294985507463045139408005)
                  ·
                    rfl

theorem cell23_5170340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_5170340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170340 prefixEnd_5170340 := by exact prefixLift 5170340
  have htrace : WordTrace (prefixWord ++ tailWord_5170340) baseStart_5170340 baseEnd_5170340 := by
    simpa [prefixWord, tailWord_5170340, baseEnd_5170340] using wordTrace_append hprefix tailTrace_5170340
  have hstable : (prefixWord ++ tailWord_5170340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170340).length < 2 ^ (prefixWord ++ tailWord_5170340).sum := by decide
  have hdescent : baseEnd_5170340 < baseStart_5170340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170383 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 8]
def baseStart_5170383 : Nat := 118140960795 + 5170383 * 2 ^ 59
def prefixEnd_5170383 : Nat := 4983230072969 + 3 ^ 40 * 5170383 * 2
def baseEnd_5170383 : Nat := 884963882278516528811449

theorem tailTrace_5170383 : CollatzResearch.WordTrace tailWord_5170383 prefixEnd_5170383 884963882278516528811449 := by
  unfold tailWord_5170383
  simp only [CollatzResearch.WordTrace]
  refine ⟨188579360427592896959811803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125719573618395264639874535 188579360427592896959811803)
  ·
    refine ⟨282869040641389345439717705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188579360427592896959811803 282869040641389345439717705)
    ·
      refine ⟨212151780481042009079788279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282869040641389345439717705 212151780481042009079788279)
      ·
        refine ⟨318227670721563013619682419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212151780481042009079788279 318227670721563013619682419)
        ·
          refine ⟨477341506082344520429523629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318227670721563013619682419 477341506082344520429523629)
          ·
            refine ⟨179003064780879195161071361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477341506082344520429523629 179003064780879195161071361)
            ·
              refine ⟨134252298585659396370803521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179003064780879195161071361 134252298585659396370803521)
              ·
                refine ⟨100689223939244547278102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134252298585659396370803521 100689223939244547278102641)
                ·
                  refine ⟨75516917954433410458576981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100689223939244547278102641 75516917954433410458576981)
                  ·
                    refine ⟨884963882278516528811449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75516917954433410458576981 884963882278516528811449)
                    ·
                      rfl

theorem cell23_5170383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_5170383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170383 prefixEnd_5170383 := by exact prefixLift 5170383
  have htrace : WordTrace (prefixWord ++ tailWord_5170383) baseStart_5170383 baseEnd_5170383 := by
    simpa [prefixWord, tailWord_5170383, baseEnd_5170383] using wordTrace_append hprefix tailTrace_5170383
  have hstable : (prefixWord ++ tailWord_5170383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170383).length < 2 ^ (prefixWord ++ tailWord_5170383).sum := by decide
  have hdescent : baseEnd_5170383 < baseStart_5170383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170461 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5170461 : Nat := 118140960795 + 5170461 * 2 ^ 59
def prefixEnd_5170461 : Nat := 4983230072969 + 3 ^ 40 * 5170461 * 2
def baseEnd_5170461 : Nat := 2654931698326600281258989

theorem tailTrace_5170461 : CollatzResearch.WordTrace tailWord_5170461 prefixEnd_5170461 2654931698326600281258989 := by
  unfold tailWord_5170461
  simp only [CollatzResearch.WordTrace]
  refine ⟨188582205321310316281151237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125721470214206877520767491 188582205321310316281151237)
  ·
    refine ⟨35359163497745684302715857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188582205321310316281151237 35359163497745684302715857)
    ·
      refine ⟨26519372623309263227036893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35359163497745684302715857 26519372623309263227036893)
      ·
        refine ⟨9944764733740973710138835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26519372623309263227036893 9944764733740973710138835)
        ·
          refine ⟨14917147100611460565208253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9944764733740973710138835 14917147100611460565208253)
          ·
            refine ⟨5593930162729297711953095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14917147100611460565208253 5593930162729297711953095)
            ·
              refine ⟨8390895244093946567929643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593930162729297711953095 8390895244093946567929643)
              ·
                refine ⟨12586342866140919851894465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8390895244093946567929643 12586342866140919851894465)
                ·
                  refine ⟨9439757149605689888920849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12586342866140919851894465 9439757149605689888920849)
                  ·
                    refine ⟨7079817862204267416690637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9439757149605689888920849 7079817862204267416690637)
                    ·
                      refine ⟨2654931698326600281258989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7079817862204267416690637 2654931698326600281258989)
                      ·
                        rfl

theorem cell23_5170461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5170461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170461 prefixEnd_5170461 := by exact prefixLift 5170461
  have htrace : WordTrace (prefixWord ++ tailWord_5170461) baseStart_5170461 baseEnd_5170461 := by
    simpa [prefixWord, tailWord_5170461, baseEnd_5170461] using wordTrace_append hprefix tailTrace_5170461
  have hstable : (prefixWord ++ tailWord_5170461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170461).length < 2 ^ (prefixWord ++ tailWord_5170461).sum := by decide
  have hdescent : baseEnd_5170461 < baseStart_5170461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170520 : List Nat := [2, 1, 2, 2, 1, 1, 5, 9]
def baseStart_5170520 : Nat := 118140960795 + 5170520 * 2 ^ 59
def prefixEnd_5170520 : Nat := 4983230072969 + 3 ^ 40 * 5170520 * 2
def baseEnd_5170520 : Nat := 98331925692045020385971

theorem tailTrace_5170520 : CollatzResearch.WordTrace tailWord_5170520 prefixEnd_5170520 98331925692045020385971 := by
  unfold tailWord_5170520
  simp only [CollatzResearch.WordTrace]
  refine ⟨94292178614048284678774507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125722904818731046238366009 94292178614048284678774507)
  ·
    refine ⟨141438267921072427018161761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94292178614048284678774507 141438267921072427018161761)
    ·
      refine ⟨106078700940804320263621321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141438267921072427018161761 106078700940804320263621321)
      ·
        refine ⟨79559025705603240197715991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106078700940804320263621321 79559025705603240197715991)
        ·
          refine ⟨119338538558404860296573987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79559025705603240197715991 119338538558404860296573987)
          ·
            refine ⟨179007807837607290444860981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119338538558404860296573987 179007807837607290444860981)
            ·
              refine ⟨16781981984775683479205717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179007807837607290444860981 16781981984775683479205717)
              ·
                refine ⟨98331925692045020385971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16781981984775683479205717 98331925692045020385971)
                ·
                  rfl

theorem cell23_5170520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 9].length) (baseStart_5170520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170520 prefixEnd_5170520 := by exact prefixLift 5170520
  have htrace : WordTrace (prefixWord ++ tailWord_5170520) baseStart_5170520 baseEnd_5170520 := by
    simpa [prefixWord, tailWord_5170520, baseEnd_5170520] using wordTrace_append hprefix tailTrace_5170520
  have hstable : (prefixWord ++ tailWord_5170520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170520).length < 2 ^ (prefixWord ++ tailWord_5170520).sum := by decide
  have hdescent : baseEnd_5170520 < baseStart_5170520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170542 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5170542 : Nat := 118140960795 + 5170542 * 2 ^ 59
def prefixEnd_5170542 : Nat := 4983230072969 + 3 ^ 40 * 5170542 * 2
def baseEnd_5170542 : Nat := 2654973290259614464346117

theorem tailTrace_5170542 : CollatzResearch.WordTrace tailWord_5170542 prefixEnd_5170542 2654973290259614464346117 := by
  unfold tailWord_5170542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23573144954252108389356235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125723439756011244743233253 23573144954252108389356235)
  ·
    refine ⟨35359717431378162584034353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23573144954252108389356235 35359717431378162584034353)
    ·
      refine ⟨26519788073533621938025765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35359717431378162584034353 26519788073533621938025765)
      ·
        refine ⟨4972460263787554113379831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26519788073533621938025765 4972460263787554113379831)
        ·
          refine ⟨7458690395681331170069747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972460263787554113379831 7458690395681331170069747)
          ·
            refine ⟨11188035593521996755104621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458690395681331170069747 11188035593521996755104621)
            ·
              refine ⟨4195513347570748783164233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11188035593521996755104621 4195513347570748783164233)
              ·
                refine ⟨3146635010678061587373175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195513347570748783164233 3146635010678061587373175)
                ·
                  refine ⟨4719952516017092381059763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3146635010678061587373175 4719952516017092381059763)
                  ·
                    refine ⟨7079928774025638571589645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4719952516017092381059763 7079928774025638571589645)
                    ·
                      refine ⟨2654973290259614464346117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7079928774025638571589645 2654973290259614464346117)
                      ·
                        rfl

theorem cell23_5170542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5170542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170542 prefixEnd_5170542 := by exact prefixLift 5170542
  have htrace : WordTrace (prefixWord ++ tailWord_5170542) baseStart_5170542 baseEnd_5170542 := by
    simpa [prefixWord, tailWord_5170542, baseEnd_5170542] using wordTrace_append hprefix tailTrace_5170542
  have hstable : (prefixWord ++ tailWord_5170542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170542).length < 2 ^ (prefixWord ++ tailWord_5170542).sum := by decide
  have hdescent : baseEnd_5170542 < baseStart_5170542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170621 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_5170621 : Nat := 118140960795 + 5170621 * 2 ^ 59
def prefixEnd_5170621 : Nat := 4983230072969 + 3 ^ 40 * 5170621 * 2
def baseEnd_5170621 : Nat := 2655013855231319655258253

theorem tailTrace_5170621 : CollatzResearch.WordTrace tailWord_5170621 prefixEnd_5170621 2655013855231319655258253 := by
  unfold tailWord_5170621
  simp only [CollatzResearch.WordTrace]
  refine ⟨188588041000730663606975717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125725360667153775737983811 188588041000730663606975717)
  ·
    refine ⟨35360257687636999426307947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188588041000730663606975717 35360257687636999426307947)
    ·
      refine ⟨53040386531455499139461921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35360257687636999426307947 53040386531455499139461921)
      ·
        refine ⟨39780289898591624354596441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53040386531455499139461921 39780289898591624354596441)
        ·
          refine ⟨29835217423943718265947331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39780289898591624354596441 29835217423943718265947331)
          ·
            refine ⟨44752826135915577398920997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29835217423943718265947331 44752826135915577398920997)
            ·
              refine ⟨8391154900484170762297687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44752826135915577398920997 8391154900484170762297687)
              ·
                refine ⟨12586732350726256143446531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391154900484170762297687 12586732350726256143446531)
                ·
                  refine ⟨18880098526089384215169797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12586732350726256143446531 18880098526089384215169797)
                  ·
                    refine ⟨3540018473641759540344337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18880098526089384215169797 3540018473641759540344337)
                    ·
                      refine ⟨2655013855231319655258253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540018473641759540344337 2655013855231319655258253)
                      ·
                        rfl

theorem cell23_5170621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_5170621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170621 prefixEnd_5170621 := by exact prefixLift 5170621
  have htrace : WordTrace (prefixWord ++ tailWord_5170621) baseStart_5170621 baseEnd_5170621 := by
    simpa [prefixWord, tailWord_5170621, baseEnd_5170621] using wordTrace_append hprefix tailTrace_5170621
  have hstable : (prefixWord ++ tailWord_5170621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170621).length < 2 ^ (prefixWord ++ tailWord_5170621).sum := by decide
  have hdescent : baseEnd_5170621 < baseStart_5170621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170661 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 5]
def baseStart_5170661 : Nat := 118140960795 + 5170661 * 2 ^ 59
def prefixEnd_5170661 : Nat := 4983230072969 + 3 ^ 40 * 5170661 * 2
def baseEnd_5170661 : Nat := 295003821606388833195341

theorem tailTrace_5170661 : CollatzResearch.WordTrace tailWord_5170661 prefixEnd_5170661 295003821606388833195341 := by
  unfold tailWord_5170661
  simp only [CollatzResearch.WordTrace]
  refine ⟨188589499920585750438431837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125726333280390500292287891 188589499920585750438431837)
  ·
    refine ⟨70721062470219656414411939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188589499920585750438431837 70721062470219656414411939)
    ·
      refine ⟨106081593705329484621617909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70721062470219656414411939 106081593705329484621617909)
      ·
        refine ⟨9945149409874639183276679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106081593705329484621617909 9945149409874639183276679)
        ·
          refine ⟨14917724114811958774915019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945149409874639183276679 14917724114811958774915019)
          ·
            refine ⟨22376586172217938162372529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14917724114811958774915019 22376586172217938162372529)
            ·
              refine ⟨16782439629163453621779397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22376586172217938162372529 16782439629163453621779397)
              ·
                refine ⟨3146707430468147554083637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16782439629163453621779397 3146707430468147554083637)
                ·
                  refine ⟨295003821606388833195341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146707430468147554083637 295003821606388833195341)
                  ·
                    rfl

theorem cell23_5170661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_5170661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170661 prefixEnd_5170661 := by exact prefixLift 5170661
  have htrace : WordTrace (prefixWord ++ tailWord_5170661) baseStart_5170661 baseEnd_5170661 := by
    simpa [prefixWord, tailWord_5170661, baseEnd_5170661] using wordTrace_append hprefix tailTrace_5170661
  have hstable : (prefixWord ++ tailWord_5170661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170661).length < 2 ^ (prefixWord ++ tailWord_5170661).sum := by decide
  have hdescent : baseEnd_5170661 < baseStart_5170661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170674 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_5170674 : Nat := 118140960795 + 5170674 * 2 ^ 59
def prefixEnd_5170674 : Nat := 4983230072969 + 3 ^ 40 * 5170674 * 2
def baseEnd_5170674 : Nat := 885013689902002649298503

theorem tailTrace_5170674 : CollatzResearch.WordTrace tailWord_5170674 prefixEnd_5170674 885013689902002649298503 := by
  unfold tailWord_5170674
  simp only [CollatzResearch.WordTrace]
  refine ⟨47147493517384663414663769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125726649379692435772436717 47147493517384663414663769)
  ·
    refine ⟨35360620138038497560997827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47147493517384663414663769 35360620138038497560997827)
    ·
      refine ⟨53040930207057746341496741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35360620138038497560997827 53040930207057746341496741)
      ·
        refine ⟨9945174413823327439030639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53040930207057746341496741 9945174413823327439030639)
        ·
          refine ⟨14917761620734991158545959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945174413823327439030639 14917761620734991158545959)
          ·
            refine ⟨22376642431102486737818939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14917761620734991158545959 22376642431102486737818939)
            ·
              refine ⟨33564963646653730106728409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22376642431102486737818939 33564963646653730106728409)
              ·
                refine ⟨25173722734990297580046307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33564963646653730106728409 25173722734990297580046307)
                ·
                  refine ⟨37760584102485446370069461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25173722734990297580046307 37760584102485446370069461)
                  ·
                    refine ⟨885013689902002649298503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37760584102485446370069461 885013689902002649298503)
                    ·
                      rfl

theorem cell23_5170674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_5170674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170674 prefixEnd_5170674 := by exact prefixLift 5170674
  have htrace : WordTrace (prefixWord ++ tailWord_5170674) baseStart_5170674 baseEnd_5170674 := by
    simpa [prefixWord, tailWord_5170674, baseEnd_5170674] using wordTrace_append hprefix tailTrace_5170674
  have hstable : (prefixWord ++ tailWord_5170674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170674).length < 2 ^ (prefixWord ++ tailWord_5170674).sum := by decide
  have hdescent : baseEnd_5170674 < baseStart_5170674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170708 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5170708 : Nat := 118140960795 + 5170708 * 2 ^ 59
def prefixEnd_5170708 : Nat := 4983230072969 + 3 ^ 40 * 5170708 * 2
def baseEnd_5170708 : Nat := 885019509349420271623451

theorem tailTrace_5170708 : CollatzResearch.WordTrace tailWord_5170708 prefixEnd_5170708 885019509349420271623451 := by
  unfold tailWord_5170708
  simp only [CollatzResearch.WordTrace]
  refine ⟨94295607075707738732696389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125727476100943651643595185 94295607075707738732696389)
  ·
    refine ⟨17680426326695201012380573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94295607075707738732696389 17680426326695201012380573)
    ·
      refine ⟨6630159872510700379642715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17680426326695201012380573 6630159872510700379642715)
      ·
        refine ⟨9945239808766050569464073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630159872510700379642715 9945239808766050569464073)
        ·
          refine ⟨7458929856574537927098055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9945239808766050569464073 7458929856574537927098055)
          ·
            refine ⟨11188394784861806890647083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458929856574537927098055 11188394784861806890647083)
            ·
              refine ⟨16782592177292710335970625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11188394784861806890647083 16782592177292710335970625)
              ·
                refine ⟨12586944132969532751977969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16782592177292710335970625 12586944132969532751977969)
                ·
                  refine ⟨9440208099727149563983477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12586944132969532751977969 9440208099727149563983477)
                  ·
                    refine ⟨885019509349420271623451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9440208099727149563983477 885019509349420271623451)
                    ·
                      rfl

theorem cell23_5170708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5170708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170708 prefixEnd_5170708 := by exact prefixLift 5170708
  have htrace : WordTrace (prefixWord ++ tailWord_5170708) baseStart_5170708 baseEnd_5170708 := by
    simpa [prefixWord, tailWord_5170708, baseEnd_5170708] using wordTrace_append hprefix tailTrace_5170708
  have hstable : (prefixWord ++ tailWord_5170708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170708).length < 2 ^ (prefixWord ++ tailWord_5170708).sum := by decide
  have hdescent : baseEnd_5170708 < baseStart_5170708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170721 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_5170721 : Nat := 118140960795 + 5170721 * 2 ^ 59
def prefixEnd_5170721 : Nat := 4983230072969 + 3 ^ 40 * 5170721 * 2
def baseEnd_5170721 : Nat := 885021734432256421335931

theorem tailTrace_5170721 : CollatzResearch.WordTrace tailWord_5170721 prefixEnd_5170721 885021734432256421335931 := by
  unfold tailWord_5170721
  simp only [CollatzResearch.WordTrace]
  refine ⟨188591688300368380685616017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125727792200245587123744011 188591688300368380685616017)
  ·
    refine ⟨141443766225276285514212013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188591688300368380685616017 141443766225276285514212013)
    ·
      refine ⟨53041412334478607067829505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141443766225276285514212013 53041412334478607067829505)
      ·
        refine ⟨39781059250858955300872129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53041412334478607067829505 39781059250858955300872129)
        ·
          refine ⟨29835794438144216475654097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39781059250858955300872129 29835794438144216475654097)
          ·
            refine ⟨22376845828608162356740573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29835794438144216475654097 22376845828608162356740573)
            ·
              refine ⟨8391317185728060883777715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22376845828608162356740573 8391317185728060883777715)
              ·
                refine ⟨12586975778592091325666573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391317185728060883777715 12586975778592091325666573)
                ·
                  refine ⟨4720115916972034247124965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12586975778592091325666573 4720115916972034247124965)
                  ·
                    refine ⟨885021734432256421335931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4720115916972034247124965 885021734432256421335931)
                    ·
                      rfl

theorem cell23_5170721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_5170721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170721 prefixEnd_5170721 := by exact prefixLift 5170721
  have htrace : WordTrace (prefixWord ++ tailWord_5170721) baseStart_5170721 baseEnd_5170721 := by
    simpa [prefixWord, tailWord_5170721, baseEnd_5170721] using wordTrace_append hprefix tailTrace_5170721
  have hstable : (prefixWord ++ tailWord_5170721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170721).length < 2 ^ (prefixWord ++ tailWord_5170721).sum := by decide
  have hdescent : baseEnd_5170721 < baseStart_5170721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170748 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_5170748 : Nat := 118140960795 + 5170748 * 2 ^ 59
def prefixEnd_5170748 : Nat := 4983230072969 + 3 ^ 40 * 5170748 * 2
def baseEnd_5170748 : Nat := 2655079067274440658370169

theorem tailTrace_5170748 : CollatzResearch.WordTrace tailWord_5170748 prefixEnd_5170748 2655079067274440658370169 := by
  unfold tailWord_5170748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94296336535635282148424449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125728448714180376197899265 94296336535635282148424449)
  ·
    refine ⟨70722252401726461611318337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94296336535635282148424449 70722252401726461611318337)
    ·
      refine ⟨53041689301294846208488753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70722252401726461611318337 53041689301294846208488753)
      ·
        refine ⟨39781266975971134656366565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53041689301294846208488753 39781266975971134656366565)
        ·
          refine ⟨7458987557994587748068731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39781266975971134656366565 7458987557994587748068731)
          ·
            refine ⟨11188481336991881622103097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458987557994587748068731 11188481336991881622103097)
            ·
              refine ⟨8391361002743911216577323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11188481336991881622103097 8391361002743911216577323)
              ·
                refine ⟨12587041504115866824865985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391361002743911216577323 12587041504115866824865985)
                ·
                  refine ⟨9440281128086900118649489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12587041504115866824865985 9440281128086900118649489)
                  ·
                    refine ⟨7080210846065175088987117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9440281128086900118649489 7080210846065175088987117)
                    ·
                      refine ⟨2655079067274440658370169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7080210846065175088987117 2655079067274440658370169)
                      ·
                        rfl

theorem cell23_5170748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_5170748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170748 prefixEnd_5170748 := by exact prefixLift 5170748
  have htrace : WordTrace (prefixWord ++ tailWord_5170748) baseStart_5170748 baseEnd_5170748 := by
    simpa [prefixWord, tailWord_5170748, baseEnd_5170748] using wordTrace_append hprefix tailTrace_5170748
  have hstable : (prefixWord ++ tailWord_5170748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170748).length < 2 ^ (prefixWord ++ tailWord_5170748).sum := by decide
  have hdescent : baseEnd_5170748 < baseStart_5170748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170805 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5170805 : Nat := 118140960795 + 5170805 * 2 ^ 59
def prefixEnd_5170805 : Nat := 4983230072969 + 3 ^ 40 * 5170805 * 2
def baseEnd_5170805 : Nat := 2655108335671746935357407

theorem tailTrace_5170805 : CollatzResearch.WordTrace tailWord_5170805 prefixEnd_5170805 2655108335671746935357407 := by
  unfold tailWord_5170805
  simp only [CollatzResearch.WordTrace]
  refine ⟨188594752032064063031673869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125729834688042708687782579 188594752032064063031673869)
  ·
    refine ⟨70723032012024023636877701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188594752032064063031673869 70723032012024023636877701)
    ·
      refine ⟨13260568502254504431914569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70723032012024023636877701 13260568502254504431914569)
      ·
        refine ⟨9945426376690878323935927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13260568502254504431914569 9945426376690878323935927)
        ·
          refine ⟨14918139565036317485903891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945426376690878323935927 14918139565036317485903891)
          ·
            refine ⟨22377209347554476228855837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918139565036317485903891 22377209347554476228855837)
            ·
              refine ⟨8391453505332928585820939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22377209347554476228855837 8391453505332928585820939)
              ·
                refine ⟨12587180257999392878731409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391453505332928585820939 12587180257999392878731409)
                ·
                  refine ⟨9440385193499544659048557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12587180257999392878731409 9440385193499544659048557)
                  ·
                    refine ⟨3540144447562329247143209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9440385193499544659048557 3540144447562329247143209)
                    ·
                      refine ⟨2655108335671746935357407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540144447562329247143209 2655108335671746935357407)
                      ·
                        rfl

theorem cell23_5170805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5170805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170805 prefixEnd_5170805 := by exact prefixLift 5170805
  have htrace : WordTrace (prefixWord ++ tailWord_5170805) baseStart_5170805 baseEnd_5170805 := by
    simpa [prefixWord, tailWord_5170805, baseEnd_5170805] using wordTrace_append hprefix tailTrace_5170805
  have hstable : (prefixWord ++ tailWord_5170805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170805).length < 2 ^ (prefixWord ++ tailWord_5170805).sum := by decide
  have hdescent : baseEnd_5170805 < baseStart_5170805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170848 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_5170848 : Nat := 118140960795 + 5170848 * 2 ^ 59
def prefixEnd_5170848 : Nat := 4983230072969 + 3 ^ 40 * 5170848 * 2
def baseEnd_5170848 : Nat := 2655130415339890267119709

theorem tailTrace_5170848 : CollatzResearch.WordTrace tailWord_5170848 prefixEnd_5170848 2655130415339890267119709 := by
  unfold tailWord_5170848
  simp only [CollatzResearch.WordTrace]
  refine ⟨94298160185454140687744599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125730880247272187583659465 94298160185454140687744599)
  ·
    refine ⟨141447240278181211031616899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94298160185454140687744599 141447240278181211031616899)
    ·
      refine ⟨212170860417271816547425349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141447240278181211031616899 212170860417271816547425349)
      ·
        refine ⟨39782036328238465602642253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212170860417271816547425349 39782036328238465602642253)
        ·
          refine ⟨14918263623089424600990845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39782036328238465602642253 14918263623089424600990845)
          ·
            refine ⟨5594348858658534225371567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14918263623089424600990845 5594348858658534225371567)
            ·
              refine ⟨8391523287987801338057351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5594348858658534225371567 8391523287987801338057351)
              ·
                refine ⟨12587284931981702007086027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391523287987801338057351 12587284931981702007086027)
                ·
                  refine ⟨18880927397972553010629041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12587284931981702007086027 18880927397972553010629041)
                  ·
                    refine ⟨14160695548479414757971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18880927397972553010629041 14160695548479414757971781)
                    ·
                      refine ⟨2655130415339890267119709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14160695548479414757971781 2655130415339890267119709)
                      ·
                        rfl

theorem cell23_5170848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_5170848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170848 prefixEnd_5170848 := by exact prefixLift 5170848
  have htrace : WordTrace (prefixWord ++ tailWord_5170848) baseStart_5170848 baseEnd_5170848 := by
    simpa [prefixWord, tailWord_5170848, baseEnd_5170848] using wordTrace_append hprefix tailTrace_5170848
  have hstable : (prefixWord ++ tailWord_5170848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170848).length < 2 ^ (prefixWord ++ tailWord_5170848).sum := by decide
  have hdescent : baseEnd_5170848 < baseStart_5170848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170864 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_5170864 : Nat := 118140960795 + 5170864 * 2 ^ 59
def prefixEnd_5170864 : Nat := 4983230072969 + 3 ^ 40 * 5170864 * 2
def baseEnd_5170864 : Nat := 2655138631030362204519635

theorem tailTrace_5170864 : CollatzResearch.WordTrace tailWord_5170864 prefixEnd_5170864 2655138631030362204519635 := by
  unfold tailWord_5170864
  simp only [CollatzResearch.WordTrace]
  refine ⟨94298451969425158054035823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125731269292566877405381097 94298451969425158054035823)
  ·
    refine ⟨141447677954137737081053735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94298451969425158054035823 141447677954137737081053735)
    ·
      refine ⟨212171516931206605621580603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141447677954137737081053735 212171516931206605621580603)
      ·
        refine ⟨318257275396809908432370905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212171516931206605621580603 318257275396809908432370905)
        ·
          refine ⟨238692956547607431324278179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318257275396809908432370905 238692956547607431324278179)
          ·
            refine ⟨358039434821411146986417269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238692956547607431324278179 358039434821411146986417269)
            ·
              refine ⟨33566197014507295029976619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 358039434821411146986417269 33566197014507295029976619)
              ·
                refine ⟨50349295521760942544964929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33566197014507295029976619 50349295521760942544964929)
                ·
                  refine ⟨37761971641320706908723697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50349295521760942544964929 37761971641320706908723697)
                  ·
                    refine ⟨28321478730990530181542773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37761971641320706908723697 28321478730990530181542773)
                    ·
                      refine ⟨2655138631030362204519635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28321478730990530181542773 2655138631030362204519635)
                      ·
                        rfl

theorem cell23_5170864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_5170864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170864 prefixEnd_5170864 := by exact prefixLift 5170864
  have htrace : WordTrace (prefixWord ++ tailWord_5170864) baseStart_5170864 baseEnd_5170864 := by
    simpa [prefixWord, tailWord_5170864, baseEnd_5170864] using wordTrace_append hprefix tailTrace_5170864
  have hstable : (prefixWord ++ tailWord_5170864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170864).length < 2 ^ (prefixWord ++ tailWord_5170864).sum := by decide
  have hdescent : baseEnd_5170864 < baseStart_5170864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170886 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5170886 : Nat := 118140960795 + 5170886 * 2 ^ 59
def prefixEnd_5170886 : Nat := 4983230072969 + 3 ^ 40 * 5170886 * 2
def baseEnd_5170886 : Nat := 2655149927604761118444535

theorem tailTrace_5170886 : CollatzResearch.WordTrace tailWord_5170886 prefixEnd_5170886 2655149927604761118444535 := by
  unfold tailWord_5170886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893678323274081683292891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125731804229847075910248341 5893678323274081683292891)
  ·
    refine ⟨8840517484911122524939337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893678323274081683292891 8840517484911122524939337)
    ·
      refine ⟨6630388113683341893704503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8840517484911122524939337 6630388113683341893704503)
      ·
        refine ⟨9945582170525012840556755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630388113683341893704503 9945582170525012840556755)
        ·
          refine ⟨14918373255787519260835133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9945582170525012840556755 14918373255787519260835133)
          ·
            refine ⟨5594389970920319722813175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14918373255787519260835133 5594389970920319722813175)
            ·
              refine ⟨8391584956380479584219763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5594389970920319722813175 8391584956380479584219763)
              ·
                refine ⟨12587377434570719376329645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391584956380479584219763 12587377434570719376329645)
                ·
                  refine ⟨4720266537964019766123617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12587377434570719376329645 4720266537964019766123617)
                  ·
                    refine ⟨3540199903473014824592713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720266537964019766123617 3540199903473014824592713)
                    ·
                      refine ⟨2655149927604761118444535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540199903473014824592713 2655149927604761118444535)
                      ·
                        rfl

theorem cell23_5170886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5170886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170886 prefixEnd_5170886 := by exact prefixLift 5170886
  have htrace : WordTrace (prefixWord ++ tailWord_5170886) baseStart_5170886 baseEnd_5170886 := by
    simpa [prefixWord, tailWord_5170886, baseEnd_5170886] using wordTrace_append hprefix tailTrace_5170886
  have hstable : (prefixWord ++ tailWord_5170886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170886).length < 2 ^ (prefixWord ++ tailWord_5170886).sum := by decide
  have hdescent : baseEnd_5170886 < baseStart_5170886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5170925 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5170925 : Nat := 118140960795 + 5170925 * 2 ^ 59
def prefixEnd_5170925 : Nat := 4983230072969 + 3 ^ 40 * 5170925 * 2
def baseEnd_5170925 : Nat := 2655169953350286465856855

theorem tailTrace_5170925 : CollatzResearch.WordTrace tailWord_5170925 prefixEnd_5170925 2655169953350286465856855 := by
  unfold tailWord_5170925
  simp only [CollatzResearch.WordTrace]
  refine ⟨188599128791629323526042229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125732752527752882350694819 188599128791629323526042229)
  ·
    refine ⟨17681168324215249080566459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188599128791629323526042229 17681168324215249080566459)
    ·
      refine ⟨26521752486322873620849689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17681168324215249080566459 26521752486322873620849689)
      ·
        refine ⟨19891314364742155215637267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26521752486322873620849689 19891314364742155215637267)
        ·
          refine ⟨29836971547113232823455901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19891314364742155215637267 29836971547113232823455901)
          ·
            refine ⟨11188864330167462308795963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29836971547113232823455901 11188864330167462308795963)
            ·
              refine ⟨16783296495251193463193945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11188864330167462308795963 16783296495251193463193945)
              ·
                refine ⟨12587472371438395097395459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16783296495251193463193945 12587472371438395097395459)
                ·
                  refine ⟨18881208557157592646093189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12587472371438395097395459 18881208557157592646093189)
                  ·
                    refine ⟨3540226604467048621142473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18881208557157592646093189 3540226604467048621142473)
                    ·
                      refine ⟨2655169953350286465856855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540226604467048621142473 2655169953350286465856855)
                      ·
                        rfl

theorem cell23_5170925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5170925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5170925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5170925 prefixEnd_5170925 := by exact prefixLift 5170925
  have htrace : WordTrace (prefixWord ++ tailWord_5170925) baseStart_5170925 baseEnd_5170925 := by
    simpa [prefixWord, tailWord_5170925, baseEnd_5170925] using wordTrace_append hprefix tailTrace_5170925
  have hstable : (prefixWord ++ tailWord_5170925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5170925).length < 2 ^ (prefixWord ++ tailWord_5170925).sum := by decide
  have hdescent : baseEnd_5170925 < baseStart_5170925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5170925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171051 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 5, 5]
def baseStart_5171051 : Nat := 118140960795 + 5171051 * 2 ^ 59
def prefixEnd_5171051 : Nat := 4983230072969 + 3 ^ 40 * 5171051 * 2
def baseEnd_5171051 : Nat := 885078217304250990960425

theorem tailTrace_5171051 : CollatzResearch.WordTrace tailWord_5171051 prefixEnd_5171051 885078217304250990960425 := by
  unfold tailWord_5171051
  simp only [CollatzResearch.WordTrace]
  refine ⟨188603724389172847045129007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125735816259448564696752671 188603724389172847045129007)
  ·
    refine ⟨282905586583759270567693511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188603724389172847045129007 282905586583759270567693511)
    ·
      refine ⟨424358379875638905851540267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282905586583759270567693511 424358379875638905851540267)
      ·
        refine ⟨636537569813458358777310401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424358379875638905851540267 636537569813458358777310401)
        ·
          refine ⟨477403177360093769082982801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636537569813458358777310401 477403177360093769082982801)
          ·
            refine ⟨358052383020070326812237101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477403177360093769082982801 358052383020070326812237101)
            ·
              refine ⟨134269643632526372554588913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358052383020070326812237101 134269643632526372554588913)
              ·
                refine ⟨100702232724394779415941685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134269643632526372554588913 100702232724394779415941685)
                ·
                  refine ⟨9440834317912010570244533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100702232724394779415941685 9440834317912010570244533)
                  ·
                    refine ⟨885078217304250990960425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9440834317912010570244533 885078217304250990960425)
                    ·
                      rfl

theorem cell23_5171051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 5].length) (baseStart_5171051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171051 prefixEnd_5171051 := by exact prefixLift 5171051
  have htrace : WordTrace (prefixWord ++ tailWord_5171051) baseStart_5171051 baseEnd_5171051 := by
    simpa [prefixWord, tailWord_5171051, baseEnd_5171051] using wordTrace_append hprefix tailTrace_5171051
  have hstable : (prefixWord ++ tailWord_5171051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171051).length < 2 ^ (prefixWord ++ tailWord_5171051).sum := by decide
  have hdescent : baseEnd_5171051 < baseStart_5171051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171071 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_5171071 : Nat := 118140960795 + 5171071 * 2 ^ 59
def prefixEnd_5171071 : Nat := 4983230072969 + 3 ^ 40 * 5171071 * 2
def baseEnd_5171071 : Nat := 2655244921525842894631183

theorem tailTrace_5171071 : CollatzResearch.WordTrace tailWord_5171071 prefixEnd_5171071 2655244921525842894631183 := by
  unfold tailWord_5171071
  simp only [CollatzResearch.WordTrace]
  refine ⟨188604453849100390460857067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125736302566066926973904711 188604453849100390460857067)
  ·
    refine ⟨282906680773650585691285601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188604453849100390460857067 282906680773650585691285601)
    ·
      refine ⟨212180010580237939268464201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282906680773650585691285601 212180010580237939268464201)
      ·
        refine ⟨159135007935178454451348151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212180010580237939268464201 159135007935178454451348151)
        ·
          refine ⟨238702511902767681677022227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159135007935178454451348151 238702511902767681677022227)
          ·
            refine ⟨358053767854151522515533341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238702511902767681677022227 358053767854151522515533341)
            ·
              refine ⟨134270162945306820943325003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358053767854151522515533341 134270162945306820943325003)
              ·
                refine ⟨201405244417960231414987505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134270162945306820943325003 201405244417960231414987505)
                ·
                  refine ⟨151053933313470173561240629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201405244417960231414987505 151053933313470173561240629)
                  ·
                    refine ⟨14161306248137828771366309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151053933313470173561240629 14161306248137828771366309)
                    ·
                      refine ⟨2655244921525842894631183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14161306248137828771366309 2655244921525842894631183)
                      ·
                        rfl

theorem cell23_5171071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_5171071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171071 prefixEnd_5171071 := by exact prefixLift 5171071
  have htrace : WordTrace (prefixWord ++ tailWord_5171071) baseStart_5171071 baseEnd_5171071 := by
    simpa [prefixWord, tailWord_5171071, baseEnd_5171071] using wordTrace_append hprefix tailTrace_5171071
  have hstable : (prefixWord ++ tailWord_5171071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171071).length < 2 ^ (prefixWord ++ tailWord_5171071).sum := by decide
  have hdescent : baseEnd_5171071 < baseStart_5171071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171088 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2]
def baseStart_5171088 : Nat := 118140960795 + 5171088 * 2 ^ 59
def prefixEnd_5171088 : Nat := 4983230072969 + 3 ^ 40 * 5171088 * 2
def baseEnd_5171088 : Nat := 2655253650696969328118605

theorem tailTrace_5171088 : CollatzResearch.WordTrace tailWord_5171088 prefixEnd_5171088 2655253650696969328118605 := by
  unfold tailWord_5171088
  simp only [CollatzResearch.WordTrace]
  refine ⟨94302536945019401182112959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125736715926692534909483945 94302536945019401182112959)
  ·
    refine ⟨141453805417529101773169439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94302536945019401182112959 141453805417529101773169439)
    ·
      refine ⟨212180708126293652659754159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141453805417529101773169439 212180708126293652659754159)
      ·
        refine ⟨318271062189440478989631239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212180708126293652659754159 318271062189440478989631239)
        ·
          refine ⟨477406593284160718484446859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318271062189440478989631239 477406593284160718484446859)
          ·
            refine ⟨716109889926241077726670289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477406593284160718484446859 716109889926241077726670289)
            ·
              refine ⟨537082417444680808295002717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716109889926241077726670289 537082417444680808295002717)
              ·
                refine ⟨201405906541755303110626019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 537082417444680808295002717 201405906541755303110626019)
                ·
                  refine ⟨302108859812632954665939029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201405906541755303110626019 302108859812632954665939029)
                  ·
                    refine ⟨3540338200929292437491473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 302108859812632954665939029 3540338200929292437491473)
                    ·
                      refine ⟨2655253650696969328118605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540338200929292437491473 2655253650696969328118605)
                      ·
                        rfl

theorem cell23_5171088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2].length) (baseStart_5171088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171088 prefixEnd_5171088 := by exact prefixLift 5171088
  have htrace : WordTrace (prefixWord ++ tailWord_5171088) baseStart_5171088 baseEnd_5171088 := by
    simpa [prefixWord, tailWord_5171088, baseEnd_5171088] using wordTrace_append hprefix tailTrace_5171088
  have hstable : (prefixWord ++ tailWord_5171088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171088).length < 2 ^ (prefixWord ++ tailWord_5171088).sum := by decide
  have hdescent : baseEnd_5171088 < baseStart_5171088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171092 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_5171092 : Nat := 118140960795 + 5171092 * 2 ^ 59
def prefixEnd_5171092 : Nat := 4983230072969 + 3 ^ 40 * 5171092 * 2
def baseEnd_5171092 : Nat := 2655255704619587312468587

theorem tailTrace_5171092 : CollatzResearch.WordTrace tailWord_5171092 prefixEnd_5171092 2655255704619587312468587 := by
  unfold tailWord_5171092
  simp only [CollatzResearch.WordTrace]
  refine ⟨94302609891012155523685765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125736813188016207364914353 94302609891012155523685765)
  ·
    refine ⟨17681739354564779160691081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94302609891012155523685765 17681739354564779160691081)
    ·
      refine ⟨13261304515923584370518311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17681739354564779160691081 13261304515923584370518311)
      ·
        refine ⟨19891956773885376555777467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261304515923584370518311 19891956773885376555777467)
        ·
          refine ⟨29837935160828064833666201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19891956773885376555777467 29837935160828064833666201)
          ·
            refine ⟨22378451370621048625249651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29837935160828064833666201 22378451370621048625249651)
            ·
              refine ⟨33567677055931572937874477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378451370621048625249651 33567677055931572937874477)
              ·
                refine ⟨12587878895974339851702929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33567677055931572937874477 12587878895974339851702929)
                ·
                  refine ⟨9440909171980754888777197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12587878895974339851702929 9440909171980754888777197)
                  ·
                    refine ⟨3540340939492783083291449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9440909171980754888777197 3540340939492783083291449)
                    ·
                      refine ⟨2655255704619587312468587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540340939492783083291449 2655255704619587312468587)
                      ·
                        rfl

theorem cell23_5171092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_5171092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171092 prefixEnd_5171092 := by exact prefixLift 5171092
  have htrace : WordTrace (prefixWord ++ tailWord_5171092) baseStart_5171092 baseEnd_5171092 := by
    simpa [prefixWord, tailWord_5171092, baseEnd_5171092] using wordTrace_append hprefix tailTrace_5171092
  have hstable : (prefixWord ++ tailWord_5171092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171092).length < 2 ^ (prefixWord ++ tailWord_5171092).sum := by decide
  have hdescent : baseEnd_5171092 < baseStart_5171092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171098 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_5171098 : Nat := 118140960795 + 5171098 * 2 ^ 59
def prefixEnd_5171098 : Nat := 4983230072969 + 3 ^ 40 * 5171098 * 2
def baseEnd_5171098 : Nat := 885086261834504762997853

theorem tailTrace_5171098 : CollatzResearch.WordTrace tailWord_5171098 prefixEnd_5171098 885086261834504762997853 := by
  unfold tailWord_5171098
  simp only [CollatzResearch.WordTrace]
  refine ⟨47151359655000643518022487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125736959080001716048059965 47151359655000643518022487)
  ·
    refine ⟨70727039482500965277033731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47151359655000643518022487 70727039482500965277033731)
    ·
      refine ⟨106090559223751447915550597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70727039482500965277033731 106090559223751447915550597)
      ·
        refine ⟨19891979854453396484165737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106090559223751447915550597 19891979854453396484165737)
        ·
          refine ⟨14918984890840047363124303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19891979854453396484165737 14918984890840047363124303)
          ·
            refine ⟨22378477336260071044686455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918984890840047363124303 22378477336260071044686455)
            ·
              refine ⟨33567716004390106567029683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378477336260071044686455 33567716004390106567029683)
              ·
                refine ⟨50351574006585159850544525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33567716004390106567029683 50351574006585159850544525)
                ·
                  refine ⟨18881840252469434943954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50351574006585159850544525 18881840252469434943954197)
                  ·
                    refine ⟨885086261834504762997853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18881840252469434943954197 885086261834504762997853)
                    ·
                      rfl

theorem cell23_5171098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_5171098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171098 prefixEnd_5171098 := by exact prefixLift 5171098
  have htrace : WordTrace (prefixWord ++ tailWord_5171098) baseStart_5171098 baseEnd_5171098 := by
    simpa [prefixWord, tailWord_5171098, baseEnd_5171098] using wordTrace_append hprefix tailTrace_5171098
  have hstable : (prefixWord ++ tailWord_5171098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171098).length < 2 ^ (prefixWord ++ tailWord_5171098).sum := by decide
  have hdescent : baseEnd_5171098 < baseStart_5171098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171125 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_5171125 : Nat := 118140960795 + 5171125 * 2 ^ 59
def prefixEnd_5171125 : Nat := 4983230072969 + 3 ^ 40 * 5171125 * 2
def baseEnd_5171125 : Nat := 2655272649481185683355935

theorem tailTrace_5171125 : CollatzResearch.WordTrace tailWord_5171125 prefixEnd_5171125 2655272649481185683355935 := by
  unfold tailWord_5171125
  simp only [CollatzResearch.WordTrace]
  refine ⟨188606423390904757683322829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125737615593936505122215219 188606423390904757683322829)
  ·
    refine ⟨70727408771589284131246061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188606423390904757683322829 70727408771589284131246061)
    ·
      refine ⟨26522778289345981549217273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70727408771589284131246061 26522778289345981549217273)
      ·
        refine ⟨19892083717009486161912955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26522778289345981549217273 19892083717009486161912955)
        ·
          refine ⟨29838125575514229242869433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19892083717009486161912955 29838125575514229242869433)
          ·
            refine ⟨22378594181635671932152075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29838125575514229242869433 22378594181635671932152075)
            ·
              refine ⟨33567891272453507898228113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378594181635671932152075 33567891272453507898228113)
              ·
                refine ⟨25175918454340130923671085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33567891272453507898228113 25175918454340130923671085)
                ·
                  refine ⟨9440969420377549096376657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25175918454340130923671085 9440969420377549096376657)
                  ·
                    refine ⟨7080727065283161822282493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9440969420377549096376657 7080727065283161822282493)
                    ·
                      refine ⟨2655272649481185683355935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7080727065283161822282493 2655272649481185683355935)
                      ·
                        rfl

theorem cell23_5171125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_5171125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171125 prefixEnd_5171125 := by exact prefixLift 5171125
  have htrace : WordTrace (prefixWord ++ tailWord_5171125) baseStart_5171125 baseEnd_5171125 := by
    simpa [prefixWord, tailWord_5171125, baseEnd_5171125] using wordTrace_append hprefix tailTrace_5171125
  have hstable : (prefixWord ++ tailWord_5171125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171125).length < 2 ^ (prefixWord ++ tailWord_5171125).sum := by decide
  have hdescent : baseEnd_5171125 < baseStart_5171125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_5171131 : Nat := 118140960795 + 5171131 * 2 ^ 59
def prefixEnd_5171131 : Nat := 4983230072969 + 3 ^ 40 * 5171131 * 2
def baseEnd_5171131 : Nat := 2655275730365112659880907

theorem tailTrace_5171131 : CollatzResearch.WordTrace tailWord_5171131 prefixEnd_5171131 2655275730365112659880907 := by
  unfold tailWord_5171131
  simp only [CollatzResearch.WordTrace]
  refine ⟨188606642228883020708041247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125737761485922013805360831 188606642228883020708041247)
  ·
    refine ⟨282909963343324531062061871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188606642228883020708041247 282909963343324531062061871)
    ·
      refine ⟨424364945014986796593092807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282909963343324531062061871 424364945014986796593092807)
      ·
        refine ⟨636547417522480194889639211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424364945014986796593092807 636547417522480194889639211)
        ·
          refine ⟨954821126283720292334458817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636547417522480194889639211 954821126283720292334458817)
          ·
            refine ⟨716115844712790219250844113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954821126283720292334458817 716115844712790219250844113)
            ·
              refine ⟨537086883534592664438133085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716115844712790219250844113 537086883534592664438133085)
              ·
                refine ⟨201407581325472249164299907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 537086883534592664438133085 201407581325472249164299907)
                ·
                  refine ⟨302111371988208373746449861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201407581325472249164299907 302111371988208373746449861)
                  ·
                    refine ⟨56645882247789070077459349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302111371988208373746449861 56645882247789070077459349)
                    ·
                      refine ⟨2655275730365112659880907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56645882247789070077459349 2655275730365112659880907)
                      ·
                        rfl

theorem cell23_5171131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_5171131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171131 prefixEnd_5171131 := by exact prefixLift 5171131
  have htrace : WordTrace (prefixWord ++ tailWord_5171131) baseStart_5171131 baseEnd_5171131 := by
    simpa [prefixWord, tailWord_5171131, baseEnd_5171131] using wordTrace_append hprefix tailTrace_5171131
  have hstable : (prefixWord ++ tailWord_5171131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171131).length < 2 ^ (prefixWord ++ tailWord_5171131).sum := by decide
  have hdescent : baseEnd_5171131 < baseStart_5171131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171132 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_5171132 : Nat := 118140960795 + 5171132 * 2 ^ 59
def prefixEnd_5171132 : Nat := 4983230072969 + 3 ^ 40 * 5171132 * 2
def baseEnd_5171132 : Nat := 885092081281922385322801

theorem tailTrace_5171132 : CollatzResearch.WordTrace tailWord_5171132 prefixEnd_5171132 885092081281922385322801 := by
  unfold tailWord_5171132
  simp only [CollatzResearch.WordTrace]
  refine ⟨94303339350939698939413825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125737785801252931919218433 94303339350939698939413825)
  ·
    refine ⟨70727504513204774204560369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94303339350939698939413825 70727504513204774204560369)
    ·
      refine ⟨53045628384903580653420277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70727504513204774204560369 53045628384903580653420277)
      ·
        refine ⟨4973027661084710686258151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53045628384903580653420277 4973027661084710686258151)
        ·
          refine ⟨7459541491627066029387227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973027661084710686258151 7459541491627066029387227)
          ·
            refine ⟨11189312237440599044080841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459541491627066029387227 11189312237440599044080841)
            ·
              refine ⟨8391984178080449283060631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11189312237440599044080841 8391984178080449283060631)
              ·
                refine ⟨12587976267120673924590947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8391984178080449283060631 12587976267120673924590947)
                ·
                  refine ⟨18881964400681010886886421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12587976267120673924590947 18881964400681010886886421)
                  ·
                    refine ⟨885092081281922385322801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18881964400681010886886421 885092081281922385322801)
                    ·
                      rfl

theorem cell23_5171132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_5171132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171132 prefixEnd_5171132 := by exact prefixLift 5171132
  have htrace : WordTrace (prefixWord ++ tailWord_5171132) baseStart_5171132 baseEnd_5171132 := by
    simpa [prefixWord, tailWord_5171132, baseEnd_5171132] using wordTrace_append hprefix tailTrace_5171132
  have hstable : (prefixWord ++ tailWord_5171132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171132).length < 2 ^ (prefixWord ++ tailWord_5171132).sum := by decide
  have hdescent : baseEnd_5171132 < baseStart_5171132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171156 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5171156 : Nat := 118140960795 + 5171156 * 2 ^ 59
def prefixEnd_5171156 : Nat := 4983230072969 + 3 ^ 40 * 5171156 * 2
def baseEnd_5171156 : Nat := 2655288567381475062068293

theorem tailTrace_5171156 : CollatzResearch.WordTrace tailWord_5171156 prefixEnd_5171156 2655288567381475062068293 := by
  unfold tailWord_5171156
  simp only [CollatzResearch.WordTrace]
  refine ⟨94303777026896224988850661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125738369369194966651800881 94303777026896224988850661)
  ·
    refine ⟨17681958192543042185409499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94303777026896224988850661 17681958192543042185409499)
    ·
      refine ⟨26522937288814563278114249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17681958192543042185409499 26522937288814563278114249)
      ·
        refine ⟨19892202966610922458585687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26522937288814563278114249 19892202966610922458585687)
        ·
          refine ⟨29838304449916383687878531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19892202966610922458585687 29838304449916383687878531)
          ·
            refine ⟨44757456674874575531817797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29838304449916383687878531 44757456674874575531817797)
            ·
              refine ⟨8392023126538982912215837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44757456674874575531817797 8392023126538982912215837)
              ·
                refine ⟨3147008672452118592080939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8392023126538982912215837 3147008672452118592080939)
                ·
                  refine ⟨4720513008678177888121409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147008672452118592080939 4720513008678177888121409)
                  ·
                    refine ⟨3540384756508633416091057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720513008678177888121409 3540384756508633416091057)
                    ·
                      refine ⟨2655288567381475062068293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540384756508633416091057 2655288567381475062068293)
                      ·
                        rfl

theorem cell23_5171156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5171156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171156 prefixEnd_5171156 := by exact prefixLift 5171156
  have htrace : WordTrace (prefixWord ++ tailWord_5171156) baseStart_5171156 baseEnd_5171156 := by
    simpa [prefixWord, tailWord_5171156, baseEnd_5171156] using wordTrace_append hprefix tailTrace_5171156
  have hstable : (prefixWord ++ tailWord_5171156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171156).length < 2 ^ (prefixWord ++ tailWord_5171156).sum := by decide
  have hdescent : baseEnd_5171156 < baseStart_5171156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171212 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_5171212 : Nat := 118140960795 + 5171212 * 2 ^ 59
def prefixEnd_5171212 : Nat := 4983230072969 + 3 ^ 40 * 5171212 * 2
def baseEnd_5171212 : Nat := 2655317322298126842968035

theorem tailTrace_5171212 : CollatzResearch.WordTrace tailWord_5171212 prefixEnd_5171212 2655317322298126842968035 := by
  unfold tailWord_5171212
  simp only [CollatzResearch.WordTrace]
  refine ⟨94304798270794785770869945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125739731027726381027826593 94304798270794785770869945)
  ·
    refine ⟨70728598703096089328152459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94304798270794785770869945 70728598703096089328152459)
    ·
      refine ⟨106092898054644133992228689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70728598703096089328152459 106092898054644133992228689)
      ·
        refine ⟨79569673540983100494171517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106092898054644133992228689 79569673540983100494171517)
        ·
          refine ⟨29838627577868662685314319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79569673540983100494171517 29838627577868662685314319)
          ·
            refine ⟨44757941366802994027971479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29838627577868662685314319 44757941366802994027971479)
            ·
              refine ⟨67136912050204491041957219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44757941366802994027971479 67136912050204491041957219)
              ·
                refine ⟨100705368075306736562935829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67136912050204491041957219 100705368075306736562935829)
                ·
                  refine ⟨4720564128530003276387617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100705368075306736562935829 4720564128530003276387617)
                  ·
                    refine ⟨3540423096397502457290713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720564128530003276387617 3540423096397502457290713)
                    ·
                      refine ⟨2655317322298126842968035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540423096397502457290713 2655317322298126842968035)
                      ·
                        rfl

theorem cell23_5171212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_5171212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171212 prefixEnd_5171212 := by exact prefixLift 5171212
  have htrace : WordTrace (prefixWord ++ tailWord_5171212) baseStart_5171212 baseEnd_5171212 := by
    simpa [prefixWord, tailWord_5171212, baseEnd_5171212] using wordTrace_append hprefix tailTrace_5171212
  have hstable : (prefixWord ++ tailWord_5171212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171212).length < 2 ^ (prefixWord ++ tailWord_5171212).sum := by decide
  have hdescent : baseEnd_5171212 < baseStart_5171212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171229 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_5171229 : Nat := 118140960795 + 5171229 * 2 ^ 59
def prefixEnd_5171229 : Nat := 4983230072969 + 3 ^ 40 * 5171229 * 2
def baseEnd_5171229 : Nat := 2655326051469253276455457

theorem tailTrace_5171229 : CollatzResearch.WordTrace tailWord_5171229 prefixEnd_5171229 2655326051469253276455457 := by
  unfold tailWord_5171229
  simp only [CollatzResearch.WordTrace]
  refine ⟨188610216582527983445108741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125740144388351988963405827 188610216582527983445108741)
  ·
    refine ⟨35364415609223996895957889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188610216582527983445108741 35364415609223996895957889)
    ·
      refine ⟨26523311706917997671968417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35364415609223996895957889 26523311706917997671968417)
      ·
        refine ⟨19892483780188498253976313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26523311706917997671968417 19892483780188498253976313)
        ·
          refine ⟨14919362835141373690482235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19892483780188498253976313 14919362835141373690482235)
          ·
            refine ⟨22379044252712060535723353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14919362835141373690482235 22379044252712060535723353)
            ·
              refine ⟨16784283189534045401792515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22379044252712060535723353 16784283189534045401792515)
              ·
                refine ⟨25176424784301068102688773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16784283189534045401792515 25176424784301068102688773)
                ·
                  refine ⟨4720579647056450269254145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25176424784301068102688773 4720579647056450269254145)
                  ·
                    refine ⟨3540434735292337701940609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720579647056450269254145 3540434735292337701940609)
                    ·
                      refine ⟨2655326051469253276455457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540434735292337701940609 2655326051469253276455457)
                      ·
                        rfl

theorem cell23_5171229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_5171229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171229 prefixEnd_5171229 := by exact prefixLift 5171229
  have htrace : WordTrace (prefixWord ++ tailWord_5171229) baseStart_5171229 baseEnd_5171229 := by
    simpa [prefixWord, tailWord_5171229, baseEnd_5171229] using wordTrace_append hprefix tailTrace_5171229
  have hstable : (prefixWord ++ tailWord_5171229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171229).length < 2 ^ (prefixWord ++ tailWord_5171229).sum := by decide
  have hdescent : baseEnd_5171229 < baseStart_5171229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171240 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5171240 : Nat := 118140960795 + 5171240 * 2 ^ 59
def prefixEnd_5171240 : Nat := 4983230072969 + 3 ^ 40 * 5171240 * 2
def baseEnd_5171240 : Nat := 2655331699756452733417907

theorem tailTrace_5171240 : CollatzResearch.WordTrace tailWord_5171240 prefixEnd_5171240 2655331699756452733417907 := by
  unfold tailWord_5171240
  simp only [CollatzResearch.WordTrace]
  refine ⟨94305308892744066161879587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125740411856992088215839449 94305308892744066161879587)
  ·
    refine ⟨141457963339116099242819381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94305308892744066161879587 141457963339116099242819381)
    ·
      refine ⟨13261684063042134304014317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141457963339116099242819381 13261684063042134304014317)
      ·
        refine ⟨4973131523640800364005369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13261684063042134304014317 4973131523640800364005369)
        ·
          refine ⟨3729848642730600273004027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4973131523640800364005369 3729848642730600273004027)
          ·
            refine ⟨5594772964095900409506041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729848642730600273004027 5594772964095900409506041)
            ·
              refine ⟨4196079723071925307129531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5594772964095900409506041 4196079723071925307129531)
              ·
                refine ⟨6294119584607887960694297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196079723071925307129531 6294119584607887960694297)
                ·
                  refine ⟨4720589688455915970520723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294119584607887960694297 4720589688455915970520723)
                  ·
                    refine ⟨7080884532683873955781085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4720589688455915970520723 7080884532683873955781085)
                    ·
                      refine ⟨2655331699756452733417907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7080884532683873955781085 2655331699756452733417907)
                      ·
                        rfl

theorem cell23_5171240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5171240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171240 prefixEnd_5171240 := by exact prefixLift 5171240
  have htrace : WordTrace (prefixWord ++ tailWord_5171240) baseStart_5171240 baseEnd_5171240 := by
    simpa [prefixWord, tailWord_5171240, baseEnd_5171240] using wordTrace_append hprefix tailTrace_5171240
  have hstable : (prefixWord ++ tailWord_5171240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171240).length < 2 ^ (prefixWord ++ tailWord_5171240).sum := by decide
  have hdescent : baseEnd_5171240 < baseStart_5171240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171246 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5171246 : Nat := 118140960795 + 5171246 * 2 ^ 59
def prefixEnd_5171246 : Nat := 4983230072969 + 3 ^ 40 * 5171246 * 2
def baseEnd_5171246 : Nat := 2655334780640379709942879

theorem tailTrace_5171246 : CollatzResearch.WordTrace tailWord_5171246 prefixEnd_5171246 2655334780640379709942879 := by
  unfold tailWord_5171246
  simp only [CollatzResearch.WordTrace]
  refine ⟨23576354577933299418559699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125740557748977596898985061 23576354577933299418559699)
  ·
    refine ⟨35364531866899949127839549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23576354577933299418559699 35364531866899949127839549)
    ·
      refine ⟨13261699450087480922939831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35364531866899949127839549 13261699450087480922939831)
      ·
        refine ⟨19892549175131221384409747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261699450087480922939831 19892549175131221384409747)
        ·
          refine ⟨29838823762696832076614621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19892549175131221384409747 29838823762696832076614621)
          ·
            refine ⟨11189558911011312028730483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29838823762696832076614621 11189558911011312028730483)
            ·
              refine ⟨16784338366516968043095725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189558911011312028730483 16784338366516968043095725)
              ·
                refine ⟨6294126887443863016160897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16784338366516968043095725 6294126887443863016160897)
                ·
                  refine ⟨4720595165582897262120673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294126887443863016160897 4720595165582897262120673)
                  ·
                    refine ⟨3540446374187172946590505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720595165582897262120673 3540446374187172946590505)
                    ·
                      refine ⟨2655334780640379709942879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540446374187172946590505 2655334780640379709942879)
                      ·
                        rfl

theorem cell23_5171246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5171246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171246 prefixEnd_5171246 := by exact prefixLift 5171246
  have htrace : WordTrace (prefixWord ++ tailWord_5171246) baseStart_5171246 baseEnd_5171246 := by
    simpa [prefixWord, tailWord_5171246, baseEnd_5171246] using wordTrace_append hprefix tailTrace_5171246
  have hstable : (prefixWord ++ tailWord_5171246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171246).length < 2 ^ (prefixWord ++ tailWord_5171246).sum := by decide
  have hdescent : baseEnd_5171246 < baseStart_5171246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171258 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_5171258 : Nat := 118140960795 + 5171258 * 2 ^ 59
def prefixEnd_5171258 : Nat := 4983230072969 + 3 ^ 40 * 5171258 * 2
def baseEnd_5171258 : Nat := 2655340942408233662992823

theorem tailTrace_5171258 : CollatzResearch.WordTrace tailWord_5171258 prefixEnd_5171258 2655340942408233662992823 := by
  unfold tailWord_5171258
  simp only [CollatzResearch.WordTrace]
  refine ⟨47152818574855730349478607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125740849532948614265276285 47152818574855730349478607)
  ·
    refine ⟨70729227862283595524217911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47152818574855730349478607 70729227862283595524217911)
    ·
      refine ⟨106093841793425393286326867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70729227862283595524217911 106093841793425393286326867)
      ·
        refine ⟨159140762690138089929490301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106093841793425393286326867 159140762690138089929490301)
        ·
          refine ⟨59677786008801783723558863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159140762690138089929490301 59677786008801783723558863)
          ·
            refine ⟨89516679013202675585338295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59677786008801783723558863 89516679013202675585338295)
            ·
              refine ⟨134275018519804013378007443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89516679013202675585338295 134275018519804013378007443)
              ·
                refine ⟨201412527779706020067011165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134275018519804013378007443 201412527779706020067011165)
                ·
                  refine ⟨75529697917389757525129187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201412527779706020067011165 75529697917389757525129187)
                  ·
                    refine ⟨113294546876084636287693781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75529697917389757525129187 113294546876084636287693781)
                    ·
                      refine ⟨2655340942408233662992823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113294546876084636287693781 2655340942408233662992823)
                      ·
                        rfl

theorem cell23_5171258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_5171258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171258 prefixEnd_5171258 := by exact prefixLift 5171258
  have htrace : WordTrace (prefixWord ++ tailWord_5171258) baseStart_5171258 baseEnd_5171258 := by
    simpa [prefixWord, tailWord_5171258, baseEnd_5171258] using wordTrace_append hprefix tailTrace_5171258
  have hstable : (prefixWord ++ tailWord_5171258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171258).length < 2 ^ (prefixWord ++ tailWord_5171258).sum := by decide
  have hdescent : baseEnd_5171258 < baseStart_5171258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171286 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_5171286 : Nat := 118140960795 + 5171286 * 2 ^ 59
def prefixEnd_5171286 : Nat := 4983230072969 + 3 ^ 40 * 5171286 * 2
def baseEnd_5171286 : Nat := 295039479985173283715855

theorem tailTrace_5171286 : CollatzResearch.WordTrace tailWord_5171286 prefixEnd_5171286 295039479985173283715855 := by
  unfold tailWord_5171286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788268471457592636245857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125741530362214321453289141 11788268471457592636245857)
  ·
    refine ⟨8841201353593194477184393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11788268471457592636245857 8841201353593194477184393)
    ·
      refine ⟨6630901015194895857888295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8841201353593194477184393 6630901015194895857888295)
      ·
        refine ⟨9946351522792343786832443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630901015194895857888295 9946351522792343786832443)
        ·
          refine ⟨14919527284188515680248665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9946351522792343786832443 14919527284188515680248665)
          ·
            refine ⟨11189645463141386760186499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14919527284188515680248665 11189645463141386760186499)
            ·
              refine ⟨16784468194712080140279749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189645463141386760186499 16784468194712080140279749)
              ·
                refine ⟨3147087786508515026302453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16784468194712080140279749 3147087786508515026302453)
                ·
                  refine ⟨295039479985173283715855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147087786508515026302453 295039479985173283715855)
                  ·
                    rfl

theorem cell23_5171286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_5171286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171286 prefixEnd_5171286 := by exact prefixLift 5171286
  have htrace : WordTrace (prefixWord ++ tailWord_5171286) baseStart_5171286 baseEnd_5171286 := by
    simpa [prefixWord, tailWord_5171286, baseEnd_5171286] using wordTrace_append hprefix tailTrace_5171286
  have hstable : (prefixWord ++ tailWord_5171286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171286).length < 2 ^ (prefixWord ++ tailWord_5171286).sum := by decide
  have hdescent : baseEnd_5171286 < baseStart_5171286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171305 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_5171305 : Nat := 118140960795 + 5171305 * 2 ^ 59
def prefixEnd_5171305 : Nat := 4983230072969 + 3 ^ 40 * 5171305 * 2
def baseEnd_5171305 : Nat := 2655365075998994979105107

theorem tailTrace_5171305 : CollatzResearch.WordTrace tailWord_5171305 prefixEnd_5171305 2655365075998994979105107 := by
  unfold tailWord_5171305
  simp only [CollatzResearch.WordTrace]
  refine ⟨188612988530252648424875369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125741992353501765616583579 188612988530252648424875369)
  ·
    refine ⟨141459741397689486318656527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188612988530252648424875369 141459741397689486318656527)
    ·
      refine ⟨212189612096534229477984791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141459741397689486318656527 212189612096534229477984791)
      ·
        refine ⟨318284418144801344216977187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212189612096534229477984791 318284418144801344216977187)
        ·
          refine ⟨477426627217202016325465781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318284418144801344216977187 477426627217202016325465781)
          ·
            refine ⟨44758746301612689030512417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 477426627217202016325465781 44758746301612689030512417)
            ·
              refine ⟨33569059726209516772884313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44758746301612689030512417 33569059726209516772884313)
              ·
                refine ⟨25176794794657137579663235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33569059726209516772884313 25176794794657137579663235)
                ·
                  refine ⟨37765192191985706369494853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25176794794657137579663235 37765192191985706369494853)
                  ·
                    refine ⟨7080973535997319944280285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37765192191985706369494853 7080973535997319944280285)
                    ·
                      refine ⟨2655365075998994979105107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7080973535997319944280285 2655365075998994979105107)
                      ·
                        rfl

theorem cell23_5171305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_5171305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171305 prefixEnd_5171305 := by exact prefixLift 5171305
  have htrace : WordTrace (prefixWord ++ tailWord_5171305) baseStart_5171305 baseEnd_5171305 := by
    simpa [prefixWord, tailWord_5171305, baseEnd_5171305] using wordTrace_append hprefix tailTrace_5171305
  have hstable : (prefixWord ++ tailWord_5171305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171305).length < 2 ^ (prefixWord ++ tailWord_5171305).sum := by decide
  have hdescent : baseEnd_5171305 < baseStart_5171305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171312 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_5171312 : Nat := 118140960795 + 5171312 * 2 ^ 59
def prefixEnd_5171312 : Nat := 4983230072969 + 3 ^ 40 * 5171312 * 2
def baseEnd_5171312 : Nat := 885122890121192150572525

theorem tailTrace_5171312 : CollatzResearch.WordTrace tailWord_5171312 prefixEnd_5171312 885122890121192150572525 := by
  unfold tailWord_5171312
  simp only [CollatzResearch.WordTrace]
  refine ⟨94306621920613644310190095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125742162560818192413586793 94306621920613644310190095)
  ·
    refine ⟨141459932880920466465285143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94306621920613644310190095 141459932880920466465285143)
    ·
      refine ⟨212189899321380699697927715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141459932880920466465285143 212189899321380699697927715)
      ·
        refine ⟨318284848982071049546891573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212189899321380699697927715 318284848982071049546891573)
        ·
          refine ⟨29839204592069160895021085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318284848982071049546891573 29839204592069160895021085)
          ·
            refine ⟨11189701722025935335632907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29839204592069160895021085 11189701722025935335632907)
            ·
              refine ⟨16784552583038903003449361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189701722025935335632907 16784552583038903003449361)
              ·
                refine ⟨12588414437279177252587021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16784552583038903003449361 12588414437279177252587021)
                ·
                  refine ⟨4720655413979691469720133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12588414437279177252587021 4720655413979691469720133)
                  ·
                    refine ⟨885122890121192150572525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4720655413979691469720133 885122890121192150572525)
                    ·
                      rfl

theorem cell23_5171312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_5171312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171312 prefixEnd_5171312 := by exact prefixLift 5171312
  have htrace : WordTrace (prefixWord ++ tailWord_5171312) baseStart_5171312 baseEnd_5171312 := by
    simpa [prefixWord, tailWord_5171312, baseEnd_5171312] using wordTrace_append hprefix tailTrace_5171312
  have hstable : (prefixWord ++ tailWord_5171312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171312).length < 2 ^ (prefixWord ++ tailWord_5171312).sum := by decide
  have hdescent : baseEnd_5171312 < baseStart_5171312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171342 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_5171342 : Nat := 118140960795 + 5171342 * 2 ^ 59
def prefixEnd_5171342 : Nat := 4983230072969 + 3 ^ 40 * 5171342 * 2
def baseEnd_5171342 : Nat := 295042674975912370482493

theorem tailTrace_5171342 : CollatzResearch.WordTrace tailWord_5171342 prefixEnd_5171342 295042674975912370482493 := by
  unfold tailWord_5171342
  simp only [CollatzResearch.WordTrace]
  refine ⟨23576792253889825467996535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125742892020745735829314853 23576792253889825467996535)
  ·
    refine ⟨35365188380834738201994803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23576792253889825467996535 35365188380834738201994803)
    ·
      refine ⟨53047782571252107302992205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35365188380834738201994803 53047782571252107302992205)
      ·
        refine ⟨19892918464219540238622077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53047782571252107302992205 19892918464219540238622077)
        ·
          refine ⟨7459844424082327589483279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19892918464219540238622077 7459844424082327589483279)
          ·
            refine ⟨11189766636123491384224919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459844424082327589483279 11189766636123491384224919)
            ·
              refine ⟨16784649954185237076337379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189766636123491384224919 16784649954185237076337379)
              ·
                refine ⟨25176974931277855614506069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16784649954185237076337379 25176974931277855614506069)
                ·
                  refine ⟨295042674975912370482493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25176974931277855614506069 295042674975912370482493)
                  ·
                    rfl

theorem cell23_5171342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_5171342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171342 prefixEnd_5171342 := by exact prefixLift 5171342
  have htrace : WordTrace (prefixWord ++ tailWord_5171342) baseStart_5171342 baseEnd_5171342 := by
    simpa [prefixWord, tailWord_5171342, baseEnd_5171342] using wordTrace_append hprefix tailTrace_5171342
  have hstable : (prefixWord ++ tailWord_5171342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171342).length < 2 ^ (prefixWord ++ tailWord_5171342).sum := by decide
  have hdescent : baseEnd_5171342 < baseStart_5171342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171359 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 6]
def baseStart_5171359 : Nat := 118140960795 + 5171359 * 2 ^ 59
def prefixEnd_5171359 : Nat := 4983230072969 + 3 ^ 40 * 5171359 * 2
def baseEnd_5171359 : Nat := 295043644883815307536651

theorem tailTrace_5171359 : CollatzResearch.WordTrace tailWord_5171359 prefixEnd_5171359 295043644883815307536651 := by
  unfold tailWord_5171359
  simp only [CollatzResearch.WordTrace]
  refine ⟨188614958072057015647341131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125743305381371343764894087 188614958072057015647341131)
  ·
    refine ⟨282922437108085523471011697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188614958072057015647341131 282922437108085523471011697)
    ·
      refine ⟨212191827831064142603258773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282922437108085523471011697 212191827831064142603258773)
      ·
        refine ⟨9946491929581131684527755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 212191827831064142603258773 9946491929581131684527755)
        ·
          refine ⟨14919737894371697526791633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9946491929581131684527755 14919737894371697526791633)
          ·
            refine ⟨11189803420778773145093725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14919737894371697526791633 11189803420778773145093725)
            ·
              refine ⟨4196176282792039929410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11189803420778773145093725 4196176282792039929410147)
              ·
                refine ⟨6294264424188059894115221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196176282792039929410147 6294264424188059894115221)
                ·
                  refine ⟨295043644883815307536651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6294264424188059894115221 295043644883815307536651)
                  ·
                    rfl

theorem cell23_5171359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 6].length) (baseStart_5171359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171359 prefixEnd_5171359 := by exact prefixLift 5171359
  have htrace : WordTrace (prefixWord ++ tailWord_5171359) baseStart_5171359 baseEnd_5171359 := by
    simpa [prefixWord, tailWord_5171359, baseEnd_5171359] using wordTrace_append hprefix tailTrace_5171359
  have hstable : (prefixWord ++ tailWord_5171359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171359).length < 2 ^ (prefixWord ++ tailWord_5171359).sum := by decide
  have hdescent : baseEnd_5171359 < baseStart_5171359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171385 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_5171385 : Nat := 118140960795 + 5171385 * 2 ^ 59
def prefixEnd_5171385 : Nat := 4983230072969 + 3 ^ 40 * 5171385 * 2
def baseEnd_5171385 : Nat := 885135384817118222034913

theorem tailTrace_5171385 : CollatzResearch.WordTrace tailWord_5171385 prefixEnd_5171385 885135384817118222034913 := by
  unfold tailWord_5171385
  simp only [CollatzResearch.WordTrace]
  refine ⟨188615906369962822087787609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125743937579975214725191739 188615906369962822087787609)
  ·
    refine ⟨141461929777472116565840707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188615906369962822087787609 141461929777472116565840707)
    ·
      refine ⟨212192894666208174848761061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141461929777472116565840707 212192894666208174848761061)
      ·
        refine ⟨39786167749914032784142699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212192894666208174848761061 39786167749914032784142699)
        ·
          refine ⟨59679251624871049176214049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39786167749914032784142699 59679251624871049176214049)
          ·
            refine ⟨44759438718653286882160537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59679251624871049176214049 44759438718653286882160537)
            ·
              refine ⟨33569579038989965161620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44759438718653286882160537 33569579038989965161620403)
              ·
                refine ⟨50354368558484947742430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33569579038989965161620403 50354368558484947742430605)
                ·
                  refine ⟨18882888209431855403411477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50354368558484947742430605 18882888209431855403411477)
                  ·
                    refine ⟨885135384817118222034913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18882888209431855403411477 885135384817118222034913)
                    ·
                      rfl

theorem cell23_5171385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_5171385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171385 prefixEnd_5171385 := by exact prefixLift 5171385
  have htrace : WordTrace (prefixWord ++ tailWord_5171385) baseStart_5171385 baseEnd_5171385 := by
    simpa [prefixWord, tailWord_5171385, baseEnd_5171385] using wordTrace_append hprefix tailTrace_5171385
  have hstable : (prefixWord ++ tailWord_5171385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171385).length < 2 ^ (prefixWord ++ tailWord_5171385).sum := by decide
  have hdescent : baseEnd_5171385 < baseStart_5171385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171386 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3]
def baseStart_5171386 : Nat := 118140960795 + 5171386 * 2 ^ 59
def prefixEnd_5171386 : Nat := 4983230072969 + 3 ^ 40 * 5171386 * 2
def baseEnd_5171386 : Nat := 2655406667932009162192235

theorem tailTrace_5171386 : CollatzResearch.WordTrace tailWord_5171386 prefixEnd_5171386 2655406667932009162192235 := by
  unfold tailWord_5171386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47153985710739799814643503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125743961895306132839049341 47153985710739799814643503)
  ·
    refine ⟨70730978566109699721965255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47153985710739799814643503 70730978566109699721965255)
    ·
      refine ⟨106096467849164549582947883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70730978566109699721965255 106096467849164549582947883)
      ·
        refine ⟨159144701773746824374421825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106096467849164549582947883 159144701773746824374421825)
        ·
          refine ⟨119358526330310118280816369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159144701773746824374421825 119358526330310118280816369)
          ·
            refine ⟨89518894747732588710612277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119358526330310118280816369 89518894747732588710612277)
            ·
              refine ⟨8392396382599930191619901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89518894747732588710612277 8392396382599930191619901)
              ·
                refine ⟨3147148643474973821857463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8392396382599930191619901 3147148643474973821857463)
                ·
                  refine ⟨4720722965212460732786195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147148643474973821857463 4720722965212460732786195)
                  ·
                    refine ⟨7081084447818691099179293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4720722965212460732786195 7081084447818691099179293)
                    ·
                      refine ⟨2655406667932009162192235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081084447818691099179293 2655406667932009162192235)
                      ·
                        rfl

theorem cell23_5171386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_5171386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171386 prefixEnd_5171386 := by exact prefixLift 5171386
  have htrace : WordTrace (prefixWord ++ tailWord_5171386) baseStart_5171386 baseEnd_5171386 := by
    simpa [prefixWord, tailWord_5171386, baseEnd_5171386] using wordTrace_append hprefix tailTrace_5171386
  have hstable : (prefixWord ++ tailWord_5171386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171386).length < 2 ^ (prefixWord ++ tailWord_5171386).sum := by decide
  have hdescent : baseEnd_5171386 < baseStart_5171386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171395 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3]
def baseStart_5171395 : Nat := 118140960795 + 5171395 * 2 ^ 59
def prefixEnd_5171395 : Nat := 4983230072969 + 3 ^ 40 * 5171395 * 2
def baseEnd_5171395 : Nat := 2655411289257899626979693

theorem tailTrace_5171395 : CollatzResearch.WordTrace tailWord_5171395 prefixEnd_5171395 2655411289257899626979693 := by
  unfold tailWord_5171395
  simp only [CollatzResearch.WordTrace]
  refine ⟨188616271099926593795651639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125744180733284395863767759 188616271099926593795651639)
  ·
    refine ⟨282924406649889890693477459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188616271099926593795651639 282924406649889890693477459)
    ·
      refine ⟨424386609974834836040216189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282924406649889890693477459 424386609974834836040216189)
      ·
        refine ⟨159144978740563063515081071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424386609974834836040216189 159144978740563063515081071)
        ·
          refine ⟨238717468110844595272621607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159144978740563063515081071 238717468110844595272621607)
          ·
            refine ⟨358076202166266892908932411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238717468110844595272621607 358076202166266892908932411)
            ·
              refine ⟨537114303249400339363398617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358076202166266892908932411 537114303249400339363398617)
              ·
                refine ⟨402835727437050254522548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537114303249400339363398617 402835727437050254522548963)
                ·
                  refine ⟨604253591155575381783823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402835727437050254522548963 604253591155575381783823445)
                  ·
                    refine ⟨7081096771354399005279181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 604253591155575381783823445 7081096771354399005279181)
                    ·
                      refine ⟨2655411289257899626979693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081096771354399005279181 2655411289257899626979693)
                      ·
                        rfl

theorem cell23_5171395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_5171395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171395 prefixEnd_5171395 := by exact prefixLift 5171395
  have htrace : WordTrace (prefixWord ++ tailWord_5171395) baseStart_5171395 baseEnd_5171395 := by
    simpa [prefixWord, tailWord_5171395, baseEnd_5171395] using wordTrace_append hprefix tailTrace_5171395
  have hstable : (prefixWord ++ tailWord_5171395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171395).length < 2 ^ (prefixWord ++ tailWord_5171395).sum := by decide
  have hdescent : baseEnd_5171395 < baseStart_5171395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171396 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_5171396 : Nat := 118140960795 + 5171396 * 2 ^ 59
def prefixEnd_5171396 : Nat := 4983230072969 + 3 ^ 40 * 5171396 * 2
def baseEnd_5171396 : Nat := 2655411802738554123067189

theorem tailTrace_5171396 : CollatzResearch.WordTrace tailWord_5171396 prefixEnd_5171396 2655411802738554123067189 := by
  unfold tailWord_5171396
  simp only [CollatzResearch.WordTrace]
  refine ⟨94308153786461485483219021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125744205048615313977625361 94308153786461485483219021)
  ·
    refine ⟨35365557669923057056207133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94308153786461485483219021 35365557669923057056207133)
    ·
      refine ⟨13262084126221146396077675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35365557669923057056207133 13262084126221146396077675)
      ·
        refine ⟨19893126189331719594116513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13262084126221146396077675 19893126189331719594116513)
        ·
          refine ⟨14919844641998789695587385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19893126189331719594116513 14919844641998789695587385)
          ·
            refine ⟨11189883481499092271690539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14919844641998789695587385 11189883481499092271690539)
            ·
              refine ⟨16784825222248638407535809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189883481499092271690539 16784825222248638407535809)
              ·
                refine ⟨12588618916686478805651857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16784825222248638407535809 12588618916686478805651857)
                ·
                  refine ⟨9441464187514859104238893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12588618916686478805651857 9441464187514859104238893)
                  ·
                    refine ⟨3540549070318072164089585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9441464187514859104238893 3540549070318072164089585)
                    ·
                      refine ⟨2655411802738554123067189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540549070318072164089585 2655411802738554123067189)
                      ·
                        rfl

theorem cell23_5171396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_5171396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171396 prefixEnd_5171396 := by exact prefixLift 5171396
  have htrace : WordTrace (prefixWord ++ tailWord_5171396) baseStart_5171396 baseEnd_5171396 := by
    simpa [prefixWord, tailWord_5171396, baseEnd_5171396] using wordTrace_append hprefix tailTrace_5171396
  have hstable : (prefixWord ++ tailWord_5171396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171396).length < 2 ^ (prefixWord ++ tailWord_5171396).sum := by decide
  have hdescent : baseEnd_5171396 < baseStart_5171396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171402 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_5171402 : Nat := 118140960795 + 5171402 * 2 ^ 59
def prefixEnd_5171402 : Nat := 4983230072969 + 3 ^ 40 * 5171402 * 2
def baseEnd_5171402 : Nat := 885138294540827033197387

theorem tailTrace_5171402 : CollatzResearch.WordTrace tailWord_5171402 prefixEnd_5171402 885138294540827033197387 := by
  unfold tailWord_5171402
  simp only [CollatzResearch.WordTrace]
  refine ⟨47154131602725308497789115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125744350940600822660770973 47154131602725308497789115)
  ·
    refine ⟨70731197404087962746683673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47154131602725308497789115 70731197404087962746683673)
    ·
      refine ⟨53048398053065972060012755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70731197404087962746683673 53048398053065972060012755)
      ·
        refine ⟨79572597079598958090019133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53048398053065972060012755 79572597079598958090019133)
        ·
          refine ⟨29839723904849609283757175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79572597079598958090019133 29839723904849609283757175)
          ·
            refine ⟨44759585857274413925635763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29839723904849609283757175 44759585857274413925635763)
            ·
              refine ⟨67139378785911620888453645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44759585857274413925635763 67139378785911620888453645)
              ·
                refine ⟨25177267044716857833170117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67139378785911620888453645 25177267044716857833170117)
                ·
                  refine ⟨4720737570884410843719397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25177267044716857833170117 4720737570884410843719397)
                  ·
                    refine ⟨885138294540827033197387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4720737570884410843719397 885138294540827033197387)
                    ·
                      rfl

theorem cell23_5171402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_5171402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171402 prefixEnd_5171402 := by exact prefixLift 5171402
  have htrace : WordTrace (prefixWord ++ tailWord_5171402) baseStart_5171402 baseEnd_5171402 := by
    simpa [prefixWord, tailWord_5171402, baseEnd_5171402] using wordTrace_append hprefix tailTrace_5171402
  have hstable : (prefixWord ++ tailWord_5171402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171402).length < 2 ^ (prefixWord ++ tailWord_5171402).sum := by decide
  have hdescent : baseEnd_5171402 < baseStart_5171402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171429 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5171429 : Nat := 118140960795 + 5171429 * 2 ^ 59
def prefixEnd_5171429 : Nat := 4983230072969 + 3 ^ 40 * 5171429 * 2
def baseEnd_5171429 : Nat := 2655428747600152493954537

theorem tailTrace_5171429 : CollatzResearch.WordTrace tailWord_5171429 prefixEnd_5171429 2655428747600152493954537 := by
  unfold tailWord_5171429
  simp only [CollatzResearch.WordTrace]
  refine ⟨188617511181803417602389341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125745007454535611734926227 188617511181803417602389341)
  ·
    refine ⟨70731566693176281600896003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188617511181803417602389341 70731566693176281600896003)
    ·
      refine ⟨106097350039764422401344005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70731566693176281600896003 106097350039764422401344005)
      ·
        refine ⟨19893253132455829200252001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106097350039764422401344005 19893253132455829200252001)
        ·
          refine ⟨14919939849341871900189001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19893253132455829200252001 14919939849341871900189001)
          ·
            refine ⟨11189954887006403925141751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14919939849341871900189001 11189954887006403925141751)
            ·
              refine ⟨16784932330509605887712627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189954887006403925141751 16784932330509605887712627)
              ·
                refine ⟨25177398495764408831568941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16784932330509605887712627 25177398495764408831568941)
                ·
                  refine ⟨9441524435911653311838353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25177398495764408831568941 9441524435911653311838353)
                  ·
                    refine ⟨7081143326933739983878765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9441524435911653311838353 7081143326933739983878765)
                    ·
                      refine ⟨2655428747600152493954537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081143326933739983878765 2655428747600152493954537)
                      ·
                        rfl

theorem cell23_5171429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5171429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171429 prefixEnd_5171429 := by exact prefixLift 5171429
  have htrace : WordTrace (prefixWord ++ tailWord_5171429) baseStart_5171429 baseEnd_5171429 := by
    simpa [prefixWord, tailWord_5171429, baseEnd_5171429] using wordTrace_append hprefix tailTrace_5171429
  have hstable : (prefixWord ++ tailWord_5171429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171429).length < 2 ^ (prefixWord ++ tailWord_5171429).sum := by decide
  have hdescent : baseEnd_5171429 < baseStart_5171429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171460 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_5171460 : Nat := 118140960795 + 5171460 * 2 ^ 59
def prefixEnd_5171460 : Nat := 4983230072969 + 3 ^ 40 * 5171460 * 2
def baseEnd_5171460 : Nat := 2655444665500441872666895

theorem tailTrace_5171460 : CollatzResearch.WordTrace tailWord_5171460 prefixEnd_5171460 2655444665500441872666895 := by
  unfold tailWord_5171460
  simp only [CollatzResearch.WordTrace]
  refine ⟨94309320922345554948383917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125745761229794073264511889 94309320922345554948383917)
  ·
    refine ⟨35365995345879583105643969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94309320922345554948383917 35365995345879583105643969)
    ·
      refine ⟨26524496509409687329232977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35365995345879583105643969 26524496509409687329232977)
      ·
        refine ⟨19893372382057265496924733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26524496509409687329232977 19893372382057265496924733)
        ·
          refine ⟨7460014643271474561346775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19893372382057265496924733 7460014643271474561346775)
          ·
            refine ⟨11190021964907211842020163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460014643271474561346775 11190021964907211842020163)
            ·
              refine ⟨16785032947360817763030245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190021964907211842020163 16785032947360817763030245)
              ·
                refine ⟨3147193677630153330568171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16785032947360817763030245 3147193677630153330568171)
                ·
                  refine ⟨4720790516445229995852257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147193677630153330568171 4720790516445229995852257)
                  ·
                    refine ⟨3540592887333922496889193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720790516445229995852257 3540592887333922496889193)
                    ·
                      refine ⟨2655444665500441872666895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540592887333922496889193 2655444665500441872666895)
                      ·
                        rfl

theorem cell23_5171460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_5171460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171460 prefixEnd_5171460 := by exact prefixLift 5171460
  have htrace : WordTrace (prefixWord ++ tailWord_5171460) baseStart_5171460 baseEnd_5171460 := by
    simpa [prefixWord, tailWord_5171460, baseEnd_5171460] using wordTrace_append hprefix tailTrace_5171460
  have hstable : (prefixWord ++ tailWord_5171460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171460).length < 2 ^ (prefixWord ++ tailWord_5171460).sum := by decide
  have hdescent : baseEnd_5171460 < baseStart_5171460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171512 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_5171512 : Nat := 118140960795 + 5171512 * 2 ^ 59
def prefixEnd_5171512 : Nat := 4983230072969 + 3 ^ 40 * 5171512 * 2
def baseEnd_5171512 : Nat := 2655471366494475669216655

theorem tailTrace_5171512 : CollatzResearch.WordTrace tailWord_5171512 prefixEnd_5171512 2655471366494475669216655 := by
  unfold tailWord_5171512
  simp only [CollatzResearch.WordTrace]
  refine ⟨94310269220251361388830395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125747025627001815185107193 94310269220251361388830395)
  ·
    refine ⟨141465403830377042083245593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94310269220251361388830395 141465403830377042083245593)
    ·
      refine ⟨106099052872782781562434195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141465403830377042083245593 106099052872782781562434195)
      ·
        refine ⟨159148579309174172343651293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106099052872782781562434195 159148579309174172343651293)
        ·
          refine ⟨59680717240940314628869235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159148579309174172343651293 59680717240940314628869235)
          ·
            refine ⟨89521075861410471943303853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59680717240940314628869235 89521075861410471943303853)
            ·
              refine ⟨33570403448028926978738945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89521075861410471943303853 33570403448028926978738945)
              ·
                refine ⟨25177802586021695234054209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33570403448028926978738945 25177802586021695234054209)
                ·
                  refine ⟨18883351939516271425540657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25177802586021695234054209 18883351939516271425540657)
                  ·
                    refine ⟨14162513954637203569155493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18883351939516271425540657 14162513954637203569155493)
                    ·
                      refine ⟨2655471366494475669216655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14162513954637203569155493 2655471366494475669216655)
                      ·
                        rfl

theorem cell23_5171512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_5171512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171512 prefixEnd_5171512 := by exact prefixLift 5171512
  have htrace : WordTrace (prefixWord ++ tailWord_5171512) baseStart_5171512 baseEnd_5171512 := by
    simpa [prefixWord, tailWord_5171512, baseEnd_5171512] using wordTrace_append hprefix tailTrace_5171512
  have hstable : (prefixWord ++ tailWord_5171512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171512).length < 2 ^ (prefixWord ++ tailWord_5171512).sum := by decide
  have hdescent : baseEnd_5171512 < baseStart_5171512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171516 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_5171516 : Nat := 118140960795 + 5171516 * 2 ^ 59
def prefixEnd_5171516 : Nat := 4983230072969 + 3 ^ 40 * 5171516 * 2
def baseEnd_5171516 : Nat := 2655473420417093653566637

theorem tailTrace_5171516 : CollatzResearch.WordTrace tailWord_5171516 prefixEnd_5171516 2655473420417093653566637 := by
  unfold tailWord_5171516
  simp only [CollatzResearch.WordTrace]
  refine ⟨94310342166244115730403201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125747122888325487640537601 94310342166244115730403201)
  ·
    refine ⟨70732756624683086797802401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94310342166244115730403201 70732756624683086797802401)
    ·
      refine ⟨53049567468512315098351801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70732756624683086797802401 53049567468512315098351801)
      ·
        refine ⟨39787175601384236323763851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53049567468512315098351801 39787175601384236323763851)
        ·
          refine ⟨59680763402076354485645777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39787175601384236323763851 59680763402076354485645777)
          ·
            refine ⟨44760572551557265864234333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59680763402076354485645777 44760572551557265864234333)
            ·
              refine ⟨16785214706833974699087875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44760572551557265864234333 16785214706833974699087875)
              ·
                refine ⟨25177822060250962048631813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16785214706833974699087875 25177822060250962048631813)
                ·
                  refine ⟨4720841636297055384118465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25177822060250962048631813 4720841636297055384118465)
                  ·
                    refine ⟨3540631227222791538088849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720841636297055384118465 3540631227222791538088849)
                    ·
                      refine ⟨2655473420417093653566637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540631227222791538088849 2655473420417093653566637)
                      ·
                        rfl

theorem cell23_5171516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_5171516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171516 prefixEnd_5171516 := by exact prefixLift 5171516
  have htrace : WordTrace (prefixWord ++ tailWord_5171516) baseStart_5171516 baseEnd_5171516 := by
    simpa [prefixWord, tailWord_5171516, baseEnd_5171516] using wordTrace_append hprefix tailTrace_5171516
  have hstable : (prefixWord ++ tailWord_5171516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171516).length < 2 ^ (prefixWord ++ tailWord_5171516).sum := by decide
  have hdescent : baseEnd_5171516 < baseStart_5171516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171573 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 5]
def baseStart_5171573 : Nat := 118140960795 + 5171573 * 2 ^ 59
def prefixEnd_5171573 : Nat := 4983230072969 + 3 ^ 40 * 5171573 * 2
def baseEnd_5171573 : Nat := 295055854312711103394875

theorem tailTrace_5171573 : CollatzResearch.WordTrace tailWord_5171573 prefixEnd_5171573 295055854312711103394875 := by
  unfold tailWord_5171573
  simp only [CollatzResearch.WordTrace]
  refine ⟨188622763293281730195631373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125748508862187820130420915 188622763293281730195631373)
  ·
    refine ⟨70733536234980648823361765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188622763293281730195631373 70733536234980648823361765)
    ·
      refine ⟨13262538044058871654380331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70733536234980648823361765 13262538044058871654380331)
      ·
        refine ⟨19893807066088307481570497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13262538044058871654380331 19893807066088307481570497)
        ·
          refine ⟨14920355299566230611177873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19893807066088307481570497 14920355299566230611177873)
          ·
            refine ⟨11190266474674672958383405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14920355299566230611177873 11190266474674672958383405)
            ·
              refine ⟨4196349928003002359393777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11190266474674672958383405 4196349928003002359393777)
              ·
                refine ⟨3147262446002251769545333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196349928003002359393777 3147262446002251769545333)
                ·
                  refine ⟨295055854312711103394875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147262446002251769545333 295055854312711103394875)
                  ·
                    rfl

theorem cell23_5171573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_5171573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171573 prefixEnd_5171573 := by exact prefixLift 5171573
  have htrace : WordTrace (prefixWord ++ tailWord_5171573) baseStart_5171573 baseEnd_5171573 := by
    simpa [prefixWord, tailWord_5171573, baseEnd_5171573] using wordTrace_append hprefix tailTrace_5171573
  have hstable : (prefixWord ++ tailWord_5171573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171573).length < 2 ^ (prefixWord ++ tailWord_5171573).sum := by decide
  have hdescent : baseEnd_5171573 < baseStart_5171573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171589 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_5171589 : Nat := 118140960795 + 5171589 * 2 ^ 59
def prefixEnd_5171589 : Nat := 4983230072969 + 3 ^ 40 * 5171589 * 2
def baseEnd_5171589 : Nat := 2655510904504871867953801

theorem tailTrace_5171589 : CollatzResearch.WordTrace tailWord_5171589 prefixEnd_5171589 2655510904504871867953801 := by
  unfold tailWord_5171589
  simp only [CollatzResearch.WordTrace]
  refine ⟨188623346861223764928213821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125748897907482509952142547 188623346861223764928213821)
  ·
    refine ⟨70733755072958911848080183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188623346861223764928213821 70733755072958911848080183)
    ·
      refine ⟨106100632609438367772120275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70733755072958911848080183 106100632609438367772120275)
      ·
        refine ⟨159150948914157551658180413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106100632609438367772120275 159150948914157551658180413)
        ·
          refine ⟨59681605842809081871817655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159150948914157551658180413 59681605842809081871817655)
          ·
            refine ⟨89522408764213622807726483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59681605842809081871817655 89522408764213622807726483)
            ·
              refine ⟨134283613146320434211589725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89522408764213622807726483 134283613146320434211589725)
              ·
                refine ⟨50356354929870162829346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134283613146320434211589725 50356354929870162829346147)
                ·
                  refine ⟨75534532394805244244019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50356354929870162829346147 75534532394805244244019221)
                  ·
                    refine ⟨3540681206006495823938401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75534532394805244244019221 3540681206006495823938401)
                    ·
                      refine ⟨2655510904504871867953801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540681206006495823938401 2655510904504871867953801)
                      ·
                        rfl

theorem cell23_5171589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_5171589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171589 prefixEnd_5171589 := by exact prefixLift 5171589
  have htrace : WordTrace (prefixWord ++ tailWord_5171589) baseStart_5171589 baseEnd_5171589 := by
    simpa [prefixWord, tailWord_5171589, baseEnd_5171589] using wordTrace_append hprefix tailTrace_5171589
  have hstable : (prefixWord ++ tailWord_5171589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171589).length < 2 ^ (prefixWord ++ tailWord_5171589).sum := by decide
  have hdescent : baseEnd_5171589 < baseStart_5171589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171633 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 1, 4]
def baseStart_5171633 : Nat := 118140960795 + 5171633 * 2 ^ 59
def prefixEnd_5171633 : Nat := 4983230072969 + 3 ^ 40 * 5171633 * 2
def baseEnd_5171633 : Nat := 885177832551223231934533

theorem tailTrace_5171633 : CollatzResearch.WordTrace tailWord_5171633 prefixEnd_5171633 885177832551223231934533 := by
  unfold tailWord_5171633
  simp only [CollatzResearch.WordTrace]
  refine ⟨188624951673064360442815553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125749967782042906961877035 188624951673064360442815553)
  ·
    refine ⟨141468713754798270332111665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188624951673064360442815553 141468713754798270332111665)
    ·
      refine ⟨106101535316098702749083749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141468713754798270332111665 106101535316098702749083749)
      ·
        refine ⟨19894037871768506765453203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106101535316098702749083749 19894037871768506765453203)
        ·
          refine ⟨29841056807652760148179805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19894037871768506765453203 29841056807652760148179805)
          ·
            refine ⟨11190396302869785055567427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29841056807652760148179805 11190396302869785055567427)
            ·
              refine ⟨16785594454304677583351141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190396302869785055567427 16785594454304677583351141)
              ·
                refine ⟨3147298960182127046878339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16785594454304677583351141 3147298960182127046878339)
                ·
                  refine ⟨4720948440273190570317509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147298960182127046878339 4720948440273190570317509)
                  ·
                    refine ⟨885177832551223231934533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4720948440273190570317509 885177832551223231934533)
                    ·
                      rfl

theorem cell23_5171633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_5171633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171633 prefixEnd_5171633 := by exact prefixLift 5171633
  have htrace : WordTrace (prefixWord ++ tailWord_5171633) baseStart_5171633 baseEnd_5171633 := by
    simpa [prefixWord, tailWord_5171633, baseEnd_5171633] using wordTrace_append hprefix tailTrace_5171633
  have hstable : (prefixWord ++ tailWord_5171633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171633).length < 2 ^ (prefixWord ++ tailWord_5171633).sum := by decide
  have hdescent : baseEnd_5171633 < baseStart_5171633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171656 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_5171656 : Nat := 118140960795 + 5171656 * 2 ^ 59
def prefixEnd_5171656 : Nat := 4983230072969 + 3 ^ 40 * 5171656 * 2
def baseEnd_5171656 : Nat := 2655545307708723105815993

theorem tailTrace_5171656 : CollatzResearch.WordTrace tailWord_5171656 prefixEnd_5171656 2655545307708723105815993 := by
  unfold tailWord_5171656
  simp only [CollatzResearch.WordTrace]
  refine ⟨94312895275990517685451411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125750527034654023580601881 94312895275990517685451411)
  ·
    refine ⟨141469342913985776528177117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94312895275990517685451411 141469342913985776528177117)
    ·
      refine ⟨53051003592744666198066419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141469342913985776528177117 53051003592744666198066419)
      ·
        refine ⟨79576505389116999297099629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53051003592744666198066419 79576505389116999297099629)
        ·
          refine ⟨29841189520918874736412361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79576505389116999297099629 29841189520918874736412361)
          ·
            refine ⟨22380892140689156052309271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29841189520918874736412361 22380892140689156052309271)
            ·
              refine ⟨33571338211033734078463907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22380892140689156052309271 33571338211033734078463907)
              ·
                refine ⟨50357007316550601117695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33571338211033734078463907 50357007316550601117695861)
                ·
                  refine ⟨4720969435926618854783987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50357007316550601117695861 4720969435926618854783987)
                  ·
                    refine ⟨7081454153889928282175981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4720969435926618854783987 7081454153889928282175981)
                    ·
                      refine ⟨2655545307708723105815993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081454153889928282175981 2655545307708723105815993)
                      ·
                        rfl

theorem cell23_5171656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_5171656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171656 prefixEnd_5171656 := by exact prefixLift 5171656
  have htrace : WordTrace (prefixWord ++ tailWord_5171656) baseStart_5171656 baseEnd_5171656 := by
    simpa [prefixWord, tailWord_5171656, baseEnd_5171656] using wordTrace_append hprefix tailTrace_5171656
  have hstable : (prefixWord ++ tailWord_5171656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171656).length < 2 ^ (prefixWord ++ tailWord_5171656).sum := by decide
  have hdescent : baseEnd_5171656 < baseStart_5171656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171659 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 1, 5]
def baseStart_5171659 : Nat := 118140960795 + 5171659 * 2 ^ 59
def prefixEnd_5171659 : Nat := 4983230072969 + 3 ^ 40 * 5171659 * 2
def baseEnd_5171659 : Nat := 885182282716895531359493

theorem tailTrace_5171659 : CollatzResearch.WordTrace tailWord_5171659 prefixEnd_5171659 885182282716895531359493 := by
  unfold tailWord_5171659
  simp only [CollatzResearch.WordTrace]
  refine ⟨188625899970970166883262031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125750599980646777922174687 188625899970970166883262031)
  ·
    refine ⟨282938849956455250324893047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188625899970970166883262031 282938849956455250324893047)
    ·
      refine ⟨424408274934682875487339571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282938849956455250324893047 424408274934682875487339571)
      ·
        refine ⟨636612412402024313231009357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424408274934682875487339571 636612412402024313231009357)
        ·
          refine ⟨238729654650759117461628509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636612412402024313231009357 238729654650759117461628509)
          ·
            refine ⟨89523620494034669048110691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238729654650759117461628509 89523620494034669048110691)
            ·
              refine ⟨134285430741052003572166037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89523620494034669048110691 134285430741052003572166037)
              ·
                refine ⟨6294629565986812667445283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134285430741052003572166037 6294629565986812667445283)
                ·
                  refine ⟨9441944348980219001167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294629565986812667445283 9441944348980219001167925)
                  ·
                    refine ⟨885182282716895531359493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9441944348980219001167925 885182282716895531359493)
                    ·
                      rfl

theorem cell23_5171659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 5].length) (baseStart_5171659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171659 prefixEnd_5171659 := by exact prefixLift 5171659
  have htrace : WordTrace (prefixWord ++ tailWord_5171659) baseStart_5171659 baseEnd_5171659 := by
    simpa [prefixWord, tailWord_5171659, baseEnd_5171659] using wordTrace_append hprefix tailTrace_5171659
  have hstable : (prefixWord ++ tailWord_5171659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171659).length < 2 ^ (prefixWord ++ tailWord_5171659).sum := by decide
  have hdescent : baseEnd_5171659 < baseStart_5171659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171660 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5171660 : Nat := 118140960795 + 5171660 * 2 ^ 59
def prefixEnd_5171660 : Nat := 4983230072969 + 3 ^ 40 * 5171660 * 2
def baseEnd_5171660 : Nat := 2655547361631341090165975

theorem tailTrace_5171660 : CollatzResearch.WordTrace tailWord_5171660 prefixEnd_5171660 2655547361631341090165975 := by
  unfold tailWord_5171660
  simp only [CollatzResearch.WordTrace]
  refine ⟨94312968221983272027024217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125750624295977696036032289 94312968221983272027024217)
  ·
    refine ⟨70734726166487454020268163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94312968221983272027024217 70734726166487454020268163)
    ·
      refine ⟨106102089249731181030402245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70734726166487454020268163 106102089249731181030402245)
      ·
        refine ⟨19894141734324596443200421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106102089249731181030402245 19894141734324596443200421)
        ·
          refine ⟨3730151575185861833100079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19894141734324596443200421 3730151575185861833100079)
          ·
            refine ⟨5595227362778792749650119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730151575185861833100079 5595227362778792749650119)
            ·
              refine ⟨8392841044168189124475179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595227362778792749650119 8392841044168189124475179)
              ·
                refine ⟨12589261566252283686712769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8392841044168189124475179 12589261566252283686712769)
                ·
                  refine ⟨9441946174689212765034577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12589261566252283686712769 9441946174689212765034577)
                  ·
                    refine ⟨7081459631016909573775933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9441946174689212765034577 7081459631016909573775933)
                    ·
                      refine ⟨2655547361631341090165975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081459631016909573775933 2655547361631341090165975)
                      ·
                        rfl

theorem cell23_5171660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5171660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171660 prefixEnd_5171660 := by exact prefixLift 5171660
  have htrace : WordTrace (prefixWord ++ tailWord_5171660) baseStart_5171660 baseEnd_5171660 := by
    simpa [prefixWord, tailWord_5171660, baseEnd_5171660] using wordTrace_append hprefix tailTrace_5171660
  have hstable : (prefixWord ++ tailWord_5171660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171660).length < 2 ^ (prefixWord ++ tailWord_5171660).sum := by decide
  have hdescent : baseEnd_5171660 < baseStart_5171660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171690 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_5171690 : Nat := 118140960795 + 5171690 * 2 ^ 59
def prefixEnd_5171690 : Nat := 4983230072969 + 3 ^ 40 * 5171690 * 2
def baseEnd_5171690 : Nat := 2655562766050975972790837

theorem tailTrace_5171690 : CollatzResearch.WordTrace tailWord_5171690 prefixEnd_5171690 2655562766050975972790837 := by
  unfold tailWord_5171690
  simp only [CollatzResearch.WordTrace]
  refine ⟨47156757658464464794410131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125751353755905239451760349 47156757658464464794410131)
  ·
    refine ⟨70735136487696697191615197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47156757658464464794410131 70735136487696697191615197)
    ·
      refine ⟨26525676182886261446855699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70735136487696697191615197 26525676182886261446855699)
      ·
        refine ⟨39788514274329392170283549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26525676182886261446855699 39788514274329392170283549)
        ·
          refine ⟨14920692852873522063856331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39788514274329392170283549 14920692852873522063856331)
          ·
            refine ⟨22381039279310283095784497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14920692852873522063856331 22381039279310283095784497)
            ·
              refine ⟨16785779459482712321838373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22381039279310283095784497 16785779459482712321838373)
              ·
                refine ⟨3147333648653008560344695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16785779459482712321838373 3147333648653008560344695)
                ·
                  refine ⟨4721000472979512840517043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147333648653008560344695 4721000472979512840517043)
                  ·
                    refine ⟨7081500709469269260775565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721000472979512840517043 7081500709469269260775565)
                    ·
                      refine ⟨2655562766050975972790837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081500709469269260775565 2655562766050975972790837)
                      ·
                        rfl

theorem cell23_5171690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_5171690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171690 prefixEnd_5171690 := by exact prefixLift 5171690
  have htrace : WordTrace (prefixWord ++ tailWord_5171690) baseStart_5171690 baseEnd_5171690 := by
    simpa [prefixWord, tailWord_5171690, baseEnd_5171690] using wordTrace_append hprefix tailTrace_5171690
  have hstable : (prefixWord ++ tailWord_5171690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171690).length < 2 ^ (prefixWord ++ tailWord_5171690).sum := by decide
  have hdescent : baseEnd_5171690 < baseStart_5171690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171699 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5]
def baseStart_5171699 : Nat := 118140960795 + 5171699 * 2 ^ 59
def prefixEnd_5171699 : Nat := 4983230072969 + 3 ^ 40 * 5171699 * 2
def baseEnd_5171699 : Nat := 2655567387376866437578295

theorem tailTrace_5171699 : CollatzResearch.WordTrace tailWord_5171699 prefixEnd_5171699 2655567387376866437578295 := by
  unfold tailWord_5171699
  simp only [CollatzResearch.WordTrace]
  refine ⟨188627358890825253714718151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125751572593883502476478767 188627358890825253714718151)
  ·
    refine ⟨282941038336237880572077227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188627358890825253714718151 282941038336237880572077227)
    ·
      refine ⟨424411557504356820858115841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282941038336237880572077227 424411557504356820858115841)
      ·
        refine ⟨318308668128267615643586881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424411557504356820858115841 318308668128267615643586881)
        ·
          refine ⟨238731501096200711732690161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318308668128267615643586881 238731501096200711732690161)
          ·
            refine ⟨179048625822150533799517621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238731501096200711732690161 179048625822150533799517621)
            ·
              refine ⟨16785808670826612543704777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179048625822150533799517621 16785808670826612543704777)
              ·
                refine ⟨12589356503119959407778583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16785808670826612543704777 12589356503119959407778583)
                ·
                  refine ⟨18884034754679939111667875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12589356503119959407778583 18884034754679939111667875)
                  ·
                    refine ⟨28326052132019908667501813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18884034754679939111667875 28326052132019908667501813)
                    ·
                      refine ⟨2655567387376866437578295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28326052132019908667501813 2655567387376866437578295)
                      ·
                        rfl

theorem cell23_5171699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_5171699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171699 prefixEnd_5171699 := by exact prefixLift 5171699
  have htrace : WordTrace (prefixWord ++ tailWord_5171699) baseStart_5171699 baseEnd_5171699 := by
    simpa [prefixWord, tailWord_5171699, baseEnd_5171699] using wordTrace_append hprefix tailTrace_5171699
  have hstable : (prefixWord ++ tailWord_5171699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171699).length < 2 ^ (prefixWord ++ tailWord_5171699).sum := by decide
  have hdescent : baseEnd_5171699 < baseStart_5171699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171709 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_5171709 : Nat := 118140960795 + 5171709 * 2 ^ 59
def prefixEnd_5171709 : Nat := 4983230072969 + 3 ^ 40 * 5171709 * 2
def baseEnd_5171709 : Nat := 2655572522183411398453249

theorem tailTrace_5171709 : CollatzResearch.WordTrace tailWord_5171709 prefixEnd_5171709 2655572522183411398453249 := by
  unfold tailWord_5171709
  simp only [CollatzResearch.WordTrace]
  refine ⟨188627723620789025422582181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125751815747192683615054787 188627723620789025422582181)
  ·
    refine ⟨35367698178897942266734159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188627723620789025422582181 35367698178897942266734159)
    ·
      refine ⟨53051547268346913400101239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35367698178897942266734159 53051547268346913400101239)
      ·
        refine ⟨79577320902520370100151859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53051547268346913400101239 79577320902520370100151859)
        ·
          refine ⟨119365981353780555150227789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79577320902520370100151859 119365981353780555150227789)
          ·
            refine ⟨44762243007667708181335421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119365981353780555150227789 44762243007667708181335421)
            ·
              refine ⟨16785841127875390568000783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44762243007667708181335421 16785841127875390568000783)
              ·
                refine ⟨25178761691813085852001175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16785841127875390568000783 25178761691813085852001175)
                ·
                  refine ⟨37768142537719628778001763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25178761691813085852001175 37768142537719628778001763)
                  ·
                    refine ⟨56652213806579443167002645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37768142537719628778001763 56652213806579443167002645)
                    ·
                      refine ⟨2655572522183411398453249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56652213806579443167002645 2655572522183411398453249)
                      ·
                        rfl

theorem cell23_5171709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_5171709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171709 prefixEnd_5171709 := by exact prefixLift 5171709
  have htrace : WordTrace (prefixWord ++ tailWord_5171709) baseStart_5171709 baseEnd_5171709 := by
    simpa [prefixWord, tailWord_5171709, baseEnd_5171709] using wordTrace_append hprefix tailTrace_5171709
  have hstable : (prefixWord ++ tailWord_5171709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171709).length < 2 ^ (prefixWord ++ tailWord_5171709).sum := by decide
  have hdescent : baseEnd_5171709 < baseStart_5171709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171713 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_5171713 : Nat := 118140960795 + 5171713 * 2 ^ 59
def prefixEnd_5171713 : Nat := 4983230072969 + 3 ^ 40 * 5171713 * 2
def baseEnd_5171713 : Nat := 2655574576106029382803231

theorem tailTrace_5171713 : CollatzResearch.WordTrace tailWord_5171713 prefixEnd_5171713 2655574576106029382803231 := by
  unfold tailWord_5171713
  simp only [CollatzResearch.WordTrace]
  refine ⟨188627869512774534105727793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125751913008516356070485195 188627869512774534105727793)
  ·
    refine ⟨141470902134580900579295845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188627869512774534105727793 141470902134580900579295845)
    ·
      refine ⟨26525794150233918858617971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141470902134580900579295845 26525794150233918858617971)
      ·
        refine ⟨39788691225350878287926957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26525794150233918858617971 39788691225350878287926957)
        ·
          refine ⟨14920759209506579357972609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39788691225350878287926957 14920759209506579357972609)
          ·
            refine ⟨11190569407129934518479457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14920759209506579357972609 11190569407129934518479457)
            ·
              refine ⟨8392927055347450888859593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11190569407129934518479457 8392927055347450888859593)
              ·
                refine ⟨6294695291510588166644695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8392927055347450888859593 6294695291510588166644695)
                ·
                  refine ⟨9442042937265882249967043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294695291510588166644695 9442042937265882249967043)
                  ·
                    refine ⟨14163064405898823374950565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9442042937265882249967043 14163064405898823374950565)
                    ·
                      refine ⟨2655574576106029382803231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14163064405898823374950565 2655574576106029382803231)
                      ·
                        rfl

theorem cell23_5171713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_5171713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171713 prefixEnd_5171713 := by exact prefixLift 5171713
  have htrace : WordTrace (prefixWord ++ tailWord_5171713) baseStart_5171713 baseEnd_5171713 := by
    simpa [prefixWord, tailWord_5171713, baseEnd_5171713] using wordTrace_append hprefix tailTrace_5171713
  have hstable : (prefixWord ++ tailWord_5171713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171713).length < 2 ^ (prefixWord ++ tailWord_5171713).sum := by decide
  have hdescent : baseEnd_5171713 < baseStart_5171713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171763 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 3]
def baseStart_5171763 : Nat := 118140960795 + 5171763 * 2 ^ 59
def prefixEnd_5171763 : Nat := 4983230072969 + 3 ^ 40 * 5171763 * 2
def baseEnd_5171763 : Nat := 2655600250138754187178001

theorem tailTrace_5171763 : CollatzResearch.WordTrace tailWord_5171763 prefixEnd_5171763 2655600250138754187178001 := by
  unfold tailWord_5171763
  simp only [CollatzResearch.WordTrace]
  refine ⟨188629693162593392645047943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125753128775062261763365295 188629693162593392645047943)
  ·
    refine ⟨282944539743890088967571915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188629693162593392645047943 282944539743890088967571915)
    ·
      refine ⟨424416809615835133451357873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282944539743890088967571915 424416809615835133451357873)
      ·
        refine ⟨318312607211876350088518405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424416809615835133451357873 318312607211876350088518405)
        ·
          refine ⟨59683613852226815641597201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318312607211876350088518405 59683613852226815641597201)
          ·
            refine ⟨44762710389170111731197901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59683613852226815641597201 44762710389170111731197901)
            ·
              refine ⟨16786016395938791899199213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44762710389170111731197901 16786016395938791899199213)
              ·
                refine ⟨6294756148477046962199705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16786016395938791899199213 6294756148477046962199705)
                ·
                  refine ⟨4721067111357785221649779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294756148477046962199705 4721067111357785221649779)
                  ·
                    refine ⟨7081600667036677832474669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721067111357785221649779 7081600667036677832474669)
                    ·
                      refine ⟨2655600250138754187178001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7081600667036677832474669 2655600250138754187178001)
                      ·
                        rfl

theorem cell23_5171763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_5171763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171763 prefixEnd_5171763 := by exact prefixLift 5171763
  have htrace : WordTrace (prefixWord ++ tailWord_5171763) baseStart_5171763 baseEnd_5171763 := by
    simpa [prefixWord, tailWord_5171763, baseEnd_5171763] using wordTrace_append hprefix tailTrace_5171763
  have hstable : (prefixWord ++ tailWord_5171763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171763).length < 2 ^ (prefixWord ++ tailWord_5171763).sum := by decide
  have hdescent : baseEnd_5171763 < baseStart_5171763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171764 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5171764 : Nat := 118140960795 + 5171764 * 2 ^ 59
def prefixEnd_5171764 : Nat := 4983230072969 + 3 ^ 40 * 5171764 * 2
def baseEnd_5171764 : Nat := 2655600763619408683265497

theorem tailTrace_5171764 : CollatzResearch.WordTrace tailWord_5171764 prefixEnd_5171764 2655600763619408683265497 := by
  unfold tailWord_5171764
  simp only [CollatzResearch.WordTrace]
  refine ⟨94314864817794884907917173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125753153090393179877222897 94314864817794884907917173)
  ·
    refine ⟨8842018576668270460117235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94314864817794884907917173 8842018576668270460117235)
    ·
      refine ⟨13263027865002405690175853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8842018576668270460117235 13263027865002405690175853)
      ·
        refine ⟨4973635449375902133815945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13263027865002405690175853 4973635449375902133815945)
        ·
          refine ⟨3730226587031926600361959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4973635449375902133815945 3730226587031926600361959)
          ·
            refine ⟨5595339880547889900542939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730226587031926600361959 5595339880547889900542939)
            ·
              refine ⟨8393009820821834850814409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595339880547889900542939 8393009820821834850814409)
              ·
                refine ⟨6294757365616376138110807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8393009820821834850814409 6294757365616376138110807)
                ·
                  refine ⟨9442136048424564207166211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294757365616376138110807 9442136048424564207166211)
                  ·
                    refine ⟨14163204072636846310749317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9442136048424564207166211 14163204072636846310749317)
                    ·
                      refine ⟨2655600763619408683265497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14163204072636846310749317 2655600763619408683265497)
                      ·
                        rfl

theorem cell23_5171764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5171764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171764 prefixEnd_5171764 := by exact prefixLift 5171764
  have htrace : WordTrace (prefixWord ++ tailWord_5171764) baseStart_5171764 baseEnd_5171764 := by
    simpa [prefixWord, tailWord_5171764, baseEnd_5171764] using wordTrace_append hprefix tailTrace_5171764
  have hstable : (prefixWord ++ tailWord_5171764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171764).length < 2 ^ (prefixWord ++ tailWord_5171764).sum := by decide
  have hdescent : baseEnd_5171764 < baseStart_5171764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171820 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_5171820 : Nat := 118140960795 + 5171820 * 2 ^ 59
def prefixEnd_5171820 : Nat := 4983230072969 + 3 ^ 40 * 5171820 * 2
def baseEnd_5171820 : Nat := 2655629518536060464165239

theorem tailTrace_5171820 : CollatzResearch.WordTrace tailWord_5171820 prefixEnd_5171820 2655629518536060464165239 := by
  unfold tailWord_5171820
  simp only [CollatzResearch.WordTrace]
  refine ⟨94315886061693445689936457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125754514748924594253248609 94315886061693445689936457)
  ·
    refine ⟨70736914546270084267452343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94315886061693445689936457 70736914546270084267452343)
    ·
      refine ⟨106105371819405126401178515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70736914546270084267452343 106105371819405126401178515)
      ·
        refine ⟨159158057729107689601767773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106105371819405126401178515 159158057729107689601767773)
        ·
          refine ⟨59684271648415383600662915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159158057729107689601767773 59684271648415383600662915)
          ·
            refine ⟨89526407472623075400994373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59684271648415383600662915 89526407472623075400994373)
            ·
              refine ⟨16786201401116826637686445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89526407472623075400994373 16786201401116826637686445)
              ·
                refine ⟨6294825525418809989132417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16786201401116826637686445 6294825525418809989132417)
                ·
                  refine ⟨4721119144064107491849313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294825525418809989132417 4721119144064107491849313)
                  ·
                    refine ⟨3540839358048080618886985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721119144064107491849313 3540839358048080618886985)
                    ·
                      refine ⟨2655629518536060464165239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540839358048080618886985 2655629518536060464165239)
                      ·
                        rfl

theorem cell23_5171820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_5171820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171820 prefixEnd_5171820 := by exact prefixLift 5171820
  have htrace : WordTrace (prefixWord ++ tailWord_5171820) baseStart_5171820 baseEnd_5171820 := by
    simpa [prefixWord, tailWord_5171820, baseEnd_5171820] using wordTrace_append hprefix tailTrace_5171820
  have hstable : (prefixWord ++ tailWord_5171820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171820).length < 2 ^ (prefixWord ++ tailWord_5171820).sum := by decide
  have hdescent : baseEnd_5171820 < baseStart_5171820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171860 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 5]
def baseStart_5171860 : Nat := 118140960795 + 5171860 * 2 ^ 59
def prefixEnd_5171860 : Nat := 4983230072969 + 3 ^ 40 * 5171860 * 2
def baseEnd_5171860 : Nat := 295072228640248923073895

theorem tailTrace_5171860 : CollatzResearch.WordTrace tailWord_5171860 prefixEnd_5171860 295072228640248923073895 := by
  unfold tailWord_5171860
  simp only [CollatzResearch.WordTrace]
  refine ⟨94316615521620989105664517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125755487362161318807552689 94316615521620989105664517)
  ·
    refine ⟨17684365410303935457312097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94316615521620989105664517 17684365410303935457312097)
    ·
      refine ⟨13263274057727951592984073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17684365410303935457312097 13263274057727951592984073)
      ·
        refine ⟨9947455543295963694738055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13263274057727951592984073 9947455543295963694738055)
        ·
          refine ⟨14921183314943945542107083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947455543295963694738055 14921183314943945542107083)
          ·
            refine ⟨22381774972415918313160625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14921183314943945542107083 22381774972415918313160625)
            ·
              refine ⟨16786331229311938734870469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22381774972415918313160625 16786331229311938734870469)
              ·
                refine ⟨3147437105495988512788213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16786331229311938734870469 3147437105495988512788213)
                ·
                  refine ⟨295072228640248923073895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147437105495988512788213 295072228640248923073895)
                  ·
                    rfl

theorem cell23_5171860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_5171860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171860 prefixEnd_5171860 := by exact prefixLift 5171860
  have htrace : WordTrace (prefixWord ++ tailWord_5171860) baseStart_5171860 baseEnd_5171860 := by
    simpa [prefixWord, tailWord_5171860, baseEnd_5171860] using wordTrace_append hprefix tailTrace_5171860
  have hstable : (prefixWord ++ tailWord_5171860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171860).length < 2 ^ (prefixWord ++ tailWord_5171860).sum := by decide
  have hdescent : baseEnd_5171860 < baseStart_5171860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171876 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_5171876 : Nat := 118140960795 + 5171876 * 2 ^ 59
def prefixEnd_5171876 : Nat := 4983230072969 + 3 ^ 40 * 5171876 * 2
def baseEnd_5171876 : Nat := 2655658273452712245064981

theorem tailTrace_5171876 : CollatzResearch.WordTrace tailWord_5171876 prefixEnd_5171876 2655658273452712245064981 := by
  unfold tailWord_5171876
  simp only [CollatzResearch.WordTrace]
  refine ⟨94316907305592006471955741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125755876407456008629274321 94316907305592006471955741)
  ·
    refine ⟨35368840239597002426983403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94316907305592006471955741 35368840239597002426983403)
    ·
      refine ⟨53053260359395503640475105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35368840239597002426983403 53053260359395503640475105)
      ·
        refine ⟨39789945269546627730356329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53053260359395503640475105 39789945269546627730356329)
        ·
          refine ⟨29842458952159970797767247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39789945269546627730356329 29842458952159970797767247)
          ·
            refine ⟨44763688428239956196650871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29842458952159970797767247 44763688428239956196650871)
            ·
              refine ⟨67145532642359934294976307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44763688428239956196650871 67145532642359934294976307)
              ·
                refine ⟨100718298963539901442464461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67145532642359934294976307 100718298963539901442464461)
                ·
                  refine ⟨37769362111327463040924173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100718298963539901442464461 37769362111327463040924173)
                  ·
                    refine ⟨14163510791747798640346565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37769362111327463040924173 14163510791747798640346565)
                    ·
                      refine ⟨2655658273452712245064981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14163510791747798640346565 2655658273452712245064981)
                      ·
                        rfl

theorem cell23_5171876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_5171876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171876 prefixEnd_5171876 := by exact prefixLift 5171876
  have htrace : WordTrace (prefixWord ++ tailWord_5171876) baseStart_5171876 baseEnd_5171876 := by
    simpa [prefixWord, tailWord_5171876, baseEnd_5171876] using wordTrace_append hprefix tailTrace_5171876
  have hstable : (prefixWord ++ tailWord_5171876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171876).length < 2 ^ (prefixWord ++ tailWord_5171876).sum := by decide
  have hdescent : baseEnd_5171876 < baseStart_5171876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171893 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5171893 : Nat := 118140960795 + 5171893 * 2 ^ 59
def prefixEnd_5171893 : Nat := 4983230072969 + 3 ^ 40 * 5171893 * 2
def baseEnd_5171893 : Nat := 2655667002623838678552403

theorem tailTrace_5171893 : CollatzResearch.WordTrace tailWord_5171893 prefixEnd_5171893 2655667002623838678552403 := by
  unfold tailWord_5171893
  simp only [CollatzResearch.WordTrace]
  refine ⟨188634434652122424847280333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125756289768081616564853555 188634434652122424847280333)
  ·
    refine ⟨70737912994545909317730125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188634434652122424847280333 70737912994545909317730125)
    ·
      refine ⟨26526717372954715994148797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70737912994545909317730125 26526717372954715994148797)
      ·
        refine ⟨9947519014858018497805799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26526717372954715994148797 9947519014858018497805799)
        ·
          refine ⟨14921278522287027746708699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947519014858018497805799 14921278522287027746708699)
          ·
            refine ⟨22381917783430541620063049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14921278522287027746708699 22381917783430541620063049)
            ·
              refine ⟨16786438337572906215047287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22381917783430541620063049 16786438337572906215047287)
              ·
                refine ⟨25179657506359359322570931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16786438337572906215047287 25179657506359359322570931)
                ·
                  refine ⟨37769486259539038983856397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25179657506359359322570931 37769486259539038983856397)
                  ·
                    refine ⟨14163557347327139618946149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37769486259539038983856397 14163557347327139618946149)
                    ·
                      refine ⟨2655667002623838678552403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14163557347327139618946149 2655667002623838678552403)
                      ·
                        rfl

theorem cell23_5171893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5171893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171893 prefixEnd_5171893 := by exact prefixLift 5171893
  have htrace : WordTrace (prefixWord ++ tailWord_5171893) baseStart_5171893 baseEnd_5171893 := by
    simpa [prefixWord, tailWord_5171893, baseEnd_5171893] using wordTrace_append hprefix tailTrace_5171893
  have hstable : (prefixWord ++ tailWord_5171893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171893).length < 2 ^ (prefixWord ++ tailWord_5171893).sum := by decide
  have hdescent : baseEnd_5171893 < baseStart_5171893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5171894 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_5171894 : Nat := 118140960795 + 5171894 * 2 ^ 59
def prefixEnd_5171894 : Nat := 4983230072969 + 3 ^ 40 * 5171894 * 2
def baseEnd_5171894 : Nat := 295074168456054797182211

theorem tailTrace_5171894 : CollatzResearch.WordTrace tailWord_5171894 prefixEnd_5171894 295074168456054797182211 := by
  unfold tailWord_5171894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11789654445319925126129171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125756314083412534678711157 11789654445319925126129171)
  ·
    refine ⟨17684481667979887689193757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11789654445319925126129171 17684481667979887689193757)
    ·
      refine ⟨6631680625492457883447659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17684481667979887689193757 6631680625492457883447659)
      ·
        refine ⟨9947520938238686825171489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6631680625492457883447659 9947520938238686825171489)
        ·
          refine ⟨7460640703679015118878617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9947520938238686825171489 7460640703679015118878617)
          ·
            refine ⟨5595480527759261339158963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7460640703679015118878617 5595480527759261339158963)
            ·
              refine ⟨8393220791638892008738445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595480527759261339158963 8393220791638892008738445)
              ·
                refine ⟨3147457796864584503276917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8393220791638892008738445 3147457796864584503276917)
                ·
                  refine ⟨295074168456054797182211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147457796864584503276917 295074168456054797182211)
                  ·
                    rfl

theorem cell23_5171894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_5171894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5171894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5171894 prefixEnd_5171894 := by exact prefixLift 5171894
  have htrace : WordTrace (prefixWord ++ tailWord_5171894) baseStart_5171894 baseEnd_5171894 := by
    simpa [prefixWord, tailWord_5171894, baseEnd_5171894] using wordTrace_append hprefix tailTrace_5171894
  have hstable : (prefixWord ++ tailWord_5171894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5171894).length < 2 ^ (prefixWord ++ tailWord_5171894).sum := by decide
  have hdescent : baseEnd_5171894 < baseStart_5171894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5171894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172004 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_5172004 : Nat := 118140960795 + 5172004 * 2 ^ 59
def prefixEnd_5172004 : Nat := 4983230072969 + 3 ^ 40 * 5172004 * 2
def baseEnd_5172004 : Nat := 2655723998976487744264393

theorem tailTrace_5172004 : CollatzResearch.WordTrace tailWord_5172004 prefixEnd_5172004 2655723998976487744264393 := by
  unfold tailWord_5172004
  simp only [CollatzResearch.WordTrace]
  refine ⟨94319241577360145402285533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125758988769813527203047377 94319241577360145402285533)
  ·
    refine ⟨35369715591510054525857075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94319241577360145402285533 35369715591510054525857075)
    ·
      refine ⟨53054573387265081788785613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35369715591510054525857075 53054573387265081788785613)
      ·
        refine ⟨19895465020224405670794605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53054573387265081788785613 19895465020224405670794605)
        ·
          refine ⟨7460799382584152126547977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19895465020224405670794605 7460799382584152126547977)
          ·
            refine ⟨5595599536938114094910983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7460799382584152126547977 5595599536938114094910983)
            ·
              refine ⟨8393399305407171142366475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595599536938114094910983 8393399305407171142366475)
              ·
                refine ⟨12590098958110756713549713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8393399305407171142366475 12590098958110756713549713)
                ·
                  refine ⟨9442574218583067535162285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12590098958110756713549713 9442574218583067535162285)
                  ·
                    refine ⟨3540965331968650325685857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9442574218583067535162285 3540965331968650325685857)
                    ·
                      refine ⟨2655723998976487744264393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3540965331968650325685857 2655723998976487744264393)
                      ·
                        rfl

theorem cell23_5172004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_5172004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172004 prefixEnd_5172004 := by exact prefixLift 5172004
  have htrace : WordTrace (prefixWord ++ tailWord_5172004) baseStart_5172004 baseEnd_5172004 := by
    simpa [prefixWord, tailWord_5172004, baseEnd_5172004] using wordTrace_append hprefix tailTrace_5172004
  have hstable : (prefixWord ++ tailWord_5172004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172004).length < 2 ^ (prefixWord ++ tailWord_5172004).sum := by decide
  have hdescent : baseEnd_5172004 < baseStart_5172004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172014 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5172014 : Nat := 118140960795 + 5172014 * 2 ^ 59
def prefixEnd_5172014 : Nat := 4983230072969 + 3 ^ 40 * 5172014 * 2
def baseEnd_5172014 : Nat := 885243044594344235046449

theorem tailTrace_5172014 : CollatzResearch.WordTrace tailWord_5172014 prefixEnd_5172014 885243044594344235046449 := by
  unfold tailWord_5172014
  simp only [CollatzResearch.WordTrace]
  refine ⟨23579855985585507814054387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125759231923122708341623397 23579855985585507814054387)
  ·
    refine ⟨35369783978378261721081581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23579855985585507814054387 35369783978378261721081581)
    ·
      refine ⟨13263668991891848145405593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35369783978378261721081581 13263668991891848145405593)
      ·
        refine ⟨9947751743918886109054195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13263668991891848145405593 9947751743918886109054195)
        ·
          refine ⟨14921627615878329163581293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9947751743918886109054195 14921627615878329163581293)
          ·
            refine ⟨5595610355954373436342985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14921627615878329163581293 5595610355954373436342985)
            ·
              refine ⟨4196707766965780077257239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5595610355954373436342985 4196707766965780077257239)
              ·
                refine ⟨6295061650448670115885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196707766965780077257239 6295061650448670115885859)
                ·
                  refine ⟨9442592475673005173828789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295061650448670115885859 9442592475673005173828789)
                  ·
                    refine ⟨885243044594344235046449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9442592475673005173828789 885243044594344235046449)
                    ·
                      rfl

theorem cell23_5172014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5172014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172014 prefixEnd_5172014 := by exact prefixLift 5172014
  have htrace : WordTrace (prefixWord ++ tailWord_5172014) baseStart_5172014 baseEnd_5172014 := by
    simpa [prefixWord, tailWord_5172014, baseEnd_5172014] using wordTrace_append hprefix tailTrace_5172014
  have hstable : (prefixWord ++ tailWord_5172014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172014).length < 2 ^ (prefixWord ++ tailWord_5172014).sum := by decide
  have hdescent : baseEnd_5172014 < baseStart_5172014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172124 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5172124 : Nat := 118140960795 + 5172124 * 2 ^ 59
def prefixEnd_5172124 : Nat := 4983230072969 + 3 ^ 40 * 5172124 * 2
def baseEnd_5172124 : Nat := 2655785616655027274763841

theorem tailTrace_5172124 : CollatzResearch.WordTrace tailWord_5172124 prefixEnd_5172124 2655785616655027274763841 := by
  unfold tailWord_5172124
  simp only [CollatzResearch.WordTrace]
  refine ⟨94321429957142775649469713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125761906609523700865959617 94321429957142775649469713)
  ·
    refine ⟨70741072467857081737102285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94321429957142775649469713 70741072467857081737102285)
    ·
      refine ⟨26527902175446405651413357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70741072467857081737102285 26527902175446405651413357)
      ·
        refine ⟨9947963315792402119280009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26527902175446405651413357 9947963315792402119280009)
        ·
          refine ⟨7460972486844301589460007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9947963315792402119280009 7460972486844301589460007)
          ·
            refine ⟨11191458730266452384190011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460972486844301589460007 11191458730266452384190011)
            ·
              refine ⟨16787188095399678576285017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11191458730266452384190011 16787188095399678576285017)
              ·
                refine ⟨12590391071549758932213763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16787188095399678576285017 12590391071549758932213763)
                ·
                  refine ⟨18885586607324638398320645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12590391071549758932213763 18885586607324638398320645)
                  ·
                    refine ⟨3541047488873369699685121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18885586607324638398320645 3541047488873369699685121)
                    ·
                      refine ⟨2655785616655027274763841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541047488873369699685121 2655785616655027274763841)
                      ·
                        rfl

theorem cell23_5172124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5172124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172124 prefixEnd_5172124 := by exact prefixLift 5172124
  have htrace : WordTrace (prefixWord ++ tailWord_5172124) baseStart_5172124 baseEnd_5172124 := by
    simpa [prefixWord, tailWord_5172124, baseEnd_5172124] using wordTrace_append hprefix tailTrace_5172124
  have hstable : (prefixWord ++ tailWord_5172124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172124).length < 2 ^ (prefixWord ++ tailWord_5172124).sum := by decide
  have hdescent : baseEnd_5172124 < baseStart_5172124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172143 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 4, 5]
def baseStart_5172143 : Nat := 118140960795 + 5172143 * 2 ^ 59
def prefixEnd_5172143 : Nat := 4983230072969 + 3 ^ 40 * 5172143 * 2
def baseEnd_5172143 : Nat := 885265124262487566808751

theorem tailTrace_5172143 : CollatzResearch.WordTrace tailWord_5172143 prefixEnd_5172143 885265124262487566808751 := by
  unfold tailWord_5172143
  simp only [CollatzResearch.WordTrace]
  refine ⟨188643552901216717543881083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125762368600811145029254055 188643552901216717543881083)
  ·
    refine ⟨282965329351825076315821625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188643552901216717543881083 282965329351825076315821625)
    ·
      refine ⟨212223997013868807236866219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282965329351825076315821625 212223997013868807236866219)
      ·
        refine ⟨318335995520803210855299329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212223997013868807236866219 318335995520803210855299329)
        ·
          refine ⟨238751996640602408141474497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318335995520803210855299329 238751996640602408141474497)
          ·
            refine ⟨179063997480451806106105873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238751996640602408141474497 179063997480451806106105873)
            ·
              refine ⟨134297998110338854579579405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179063997480451806106105873 134297998110338854579579405)
              ·
                refine ⟨50361749291377070467342277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134297998110338854579579405 50361749291377070467342277)
                ·
                  refine ⟨9442827992133200712626677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50361749291377070467342277 9442827992133200712626677)
                  ·
                    refine ⟨885265124262487566808751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9442827992133200712626677 885265124262487566808751)
                    ·
                      rfl

theorem cell23_5172143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_5172143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172143 prefixEnd_5172143 := by exact prefixLift 5172143
  have htrace : WordTrace (prefixWord ++ tailWord_5172143) baseStart_5172143 baseEnd_5172143 := by
    simpa [prefixWord, tailWord_5172143, baseEnd_5172143] using wordTrace_append hprefix tailTrace_5172143
  have hstable : (prefixWord ++ tailWord_5172143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172143).length < 2 ^ (prefixWord ++ tailWord_5172143).sum := by decide
  have hdescent : baseEnd_5172143 < baseStart_5172143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172157 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_5172157 : Nat := 118140960795 + 5172157 * 2 ^ 59
def prefixEnd_5172157 : Nat := 4983230072969 + 3 ^ 40 * 5172157 * 2
def baseEnd_5172157 : Nat := 2655802561516625645651189

theorem tailTrace_5172157 : CollatzResearch.WordTrace tailWord_5172157 prefixEnd_5172157 2655802561516625645651189 := by
  unfold tailWord_5172157
  simp only [CollatzResearch.WordTrace]
  refine ⟨188644063523165997934890725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125762709015443998623260483 188644063523165997934890725)
  ·
    refine ⟨35370761910593624612792011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188644063523165997934890725 35370761910593624612792011)
    ·
      refine ⟨53056142865890436919188017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35370761910593624612792011 53056142865890436919188017)
      ·
        refine ⟨39792107149417827689391013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53056142865890436919188017 39792107149417827689391013)
        ·
          refine ⟨7461020090515842691760815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39792107149417827689391013 7461020090515842691760815)
          ·
            refine ⟨11191530135773764037641223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461020090515842691760815 11191530135773764037641223)
            ·
              refine ⟨16787295203660646056461835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11191530135773764037641223 16787295203660646056461835)
              ·
                refine ⟨25180942805490969084692753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16787295203660646056461835 25180942805490969084692753)
                ·
                  refine ⟨18885707104118226813519565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25180942805490969084692753 18885707104118226813519565)
                  ·
                    refine ⟨7082140164044335055069837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18885707104118226813519565 7082140164044335055069837)
                    ·
                      refine ⟨2655802561516625645651189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7082140164044335055069837 2655802561516625645651189)
                      ·
                        rfl

theorem cell23_5172157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_5172157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172157 prefixEnd_5172157 := by exact prefixLift 5172157
  have htrace : WordTrace (prefixWord ++ tailWord_5172157) baseStart_5172157 baseEnd_5172157 := by
    simpa [prefixWord, tailWord_5172157, baseEnd_5172157] using wordTrace_append hprefix tailTrace_5172157
  have hstable : (prefixWord ++ tailWord_5172157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172157).length < 2 ^ (prefixWord ++ tailWord_5172157).sum := by decide
  have hdescent : baseEnd_5172157 < baseStart_5172157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172163 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_5172163 : Nat := 118140960795 + 5172163 * 2 ^ 59
def prefixEnd_5172163 : Nat := 4983230072969 + 3 ^ 40 * 5172163 * 2
def baseEnd_5172163 : Nat := 2655805642400552622176161

theorem tailTrace_5172163 : CollatzResearch.WordTrace tailWord_5172163 prefixEnd_5172163 2655805642400552622176161 := by
  unfold tailWord_5172163
  simp only [CollatzResearch.WordTrace]
  refine ⟨188644282361144260959609143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125762854907429507306406095 188644282361144260959609143)
  ·
    refine ⟨282966423541716391439413715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188644282361144260959609143 282966423541716391439413715)
    ·
      refine ⟨424449635312574587159120573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282966423541716391439413715 424449635312574587159120573)
      ·
        refine ⟨159168613242215470184670215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424449635312574587159120573 159168613242215470184670215)
        ·
          refine ⟨238752919863323205277005323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159168613242215470184670215 238752919863323205277005323)
          ·
            refine ⟨358129379794984807915507985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238752919863323205277005323 358129379794984807915507985)
            ·
              refine ⟨268597034846238605936630989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358129379794984807915507985 268597034846238605936630989)
              ·
                refine ⟨100723888067339477226236621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268597034846238605936630989 100723888067339477226236621)
                ·
                  refine ⟨37771458025252303959838733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100723888067339477226236621 37771458025252303959838733)
                  ·
                    refine ⟨14164296759469613984939525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37771458025252303959838733 14164296759469613984939525)
                    ·
                      refine ⟨2655805642400552622176161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14164296759469613984939525 2655805642400552622176161)
                      ·
                        rfl

theorem cell23_5172163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_5172163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172163 prefixEnd_5172163 := by exact prefixLift 5172163
  have htrace : WordTrace (prefixWord ++ tailWord_5172163) baseStart_5172163 baseEnd_5172163 := by
    simpa [prefixWord, tailWord_5172163, baseEnd_5172163] using wordTrace_append hprefix tailTrace_5172163
  have hstable : (prefixWord ++ tailWord_5172163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172163).length < 2 ^ (prefixWord ++ tailWord_5172163).sum := by decide
  have hdescent : baseEnd_5172163 < baseStart_5172163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172183 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_5172183 : Nat := 118140960795 + 5172183 * 2 ^ 59
def prefixEnd_5172183 : Nat := 4983230072969 + 3 ^ 40 * 5172183 * 2
def baseEnd_5172183 : Nat := 2655815912013642543926069

theorem tailTrace_5172183 : CollatzResearch.WordTrace tailWord_5172183 prefixEnd_5172183 2655815912013642543926069 := by
  unfold tailWord_5172183
  simp only [CollatzResearch.WordTrace]
  refine ⟨188645011821071804375337203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125763341214047869583558135 188645011821071804375337203)
  ·
    refine ⟨282967517731607706563005805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188645011821071804375337203 282967517731607706563005805)
    ·
      refine ⟨106112819149352889961127177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282967517731607706563005805 106112819149352889961127177)
      ·
        refine ⟨79584614362014667470845383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106112819149352889961127177 79584614362014667470845383)
        ·
          refine ⟨119376921543022001206268075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79584614362014667470845383 119376921543022001206268075)
          ·
            refine ⟨179065382314533001809402113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119376921543022001206268075 179065382314533001809402113)
            ·
              refine ⟨134299036735899751357051585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179065382314533001809402113 134299036735899751357051585)
              ·
                refine ⟨100724277551924813517788689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134299036735899751357051585 100724277551924813517788689)
                ·
                  refine ⟨75543208163943610138341517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100724277551924813517788689 75543208163943610138341517)
                  ·
                    refine ⟨28328703061478853801878069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75543208163943610138341517 28328703061478853801878069)
                    ·
                      refine ⟨2655815912013642543926069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28328703061478853801878069 2655815912013642543926069)
                      ·
                        rfl

theorem cell23_5172183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_5172183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172183 prefixEnd_5172183 := by exact prefixLift 5172183
  have htrace : WordTrace (prefixWord ++ tailWord_5172183) baseStart_5172183 baseEnd_5172183 := by
    simpa [prefixWord, tailWord_5172183, baseEnd_5172183] using wordTrace_append hprefix tailTrace_5172183
  have hstable : (prefixWord ++ tailWord_5172183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172183).length < 2 ^ (prefixWord ++ tailWord_5172183).sum := by decide
  have hdescent : baseEnd_5172183 < baseStart_5172183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172207 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 3, 4]
def baseStart_5172207 : Nat := 118140960795 + 5172207 * 2 ^ 59
def prefixEnd_5172207 : Nat := 4983230072969 + 3 ^ 40 * 5172207 * 2
def baseEnd_5172207 : Nat := 885276078516450150008653

theorem tailTrace_5172207 : CollatzResearch.WordTrace tailWord_5172207 prefixEnd_5172207 885276078516450150008653 := by
  unfold tailWord_5172207
  simp only [CollatzResearch.WordTrace]
  refine ⟨188645887172984856474210875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125763924781989904316140583 188645887172984856474210875)
  ·
    refine ⟨282968830759477284711316313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188645887172984856474210875 282968830759477284711316313)
    ·
      refine ⟨212226623069607963533487235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282968830759477284711316313 212226623069607963533487235)
      ·
        refine ⟨318339934604411945300230853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212226623069607963533487235 318339934604411945300230853)
        ·
          refine ⟨59688737738327239743793285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318339934604411945300230853 59688737738327239743793285)
          ·
            refine ⟨11191638325936357451961241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59688737738327239743793285 11191638325936357451961241)
            ·
              refine ⟨8393728744452268088970931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11191638325936357451961241 8393728744452268088970931)
              ·
                refine ⟨12590593116678402133456397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8393728744452268088970931 12590593116678402133456397)
                ·
                  refine ⟨4721472418754400800046149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12590593116678402133456397 4721472418754400800046149)
                  ·
                    refine ⟨885276078516450150008653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4721472418754400800046149 885276078516450150008653)
                    ·
                      rfl

theorem cell23_5172207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_5172207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172207 prefixEnd_5172207 := by exact prefixLift 5172207
  have htrace : WordTrace (prefixWord ++ tailWord_5172207) baseStart_5172207 baseEnd_5172207 := by
    simpa [prefixWord, tailWord_5172207, baseEnd_5172207] using wordTrace_append hprefix tailTrace_5172207
  have hstable : (prefixWord ++ tailWord_5172207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172207).length < 2 ^ (prefixWord ++ tailWord_5172207).sum := by decide
  have hdescent : baseEnd_5172207 < baseStart_5172207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172214 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5172214 : Nat := 118140960795 + 5172214 * 2 ^ 59
def prefixEnd_5172214 : Nat := 4983230072969 + 3 ^ 40 * 5172214 * 2
def baseEnd_5172214 : Nat := 2655831829913931922638427

theorem tailTrace_5172214 : CollatzResearch.WordTrace tailWord_5172214 prefixEnd_5172214 2655831829913931922638427 := by
  unfold tailWord_5172214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790383905247468541857231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125764094989306331113143797 11790383905247468541857231)
  ·
    refine ⟨17685575857871202812785847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790383905247468541857231 17685575857871202812785847)
    ·
      refine ⟨26528363786806804219178771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17685575857871202812785847 26528363786806804219178771)
      ·
        refine ⟨39792545680210206328768157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26528363786806804219178771 39792545680210206328768157)
        ·
          refine ⟨14922204630078827373288059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39792545680210206328768157 14922204630078827373288059)
          ·
            refine ⟨22383306945118241059932089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14922204630078827373288059 22383306945118241059932089)
            ·
              refine ⟨16787480208838680794949067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22383306945118241059932089 16787480208838680794949067)
              ·
                refine ⟨25181220313258021192423601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16787480208838680794949067 25181220313258021192423601)
                ·
                  refine ⟨18885915234943515894317701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25181220313258021192423601 18885915234943515894317701)
                  ·
                    refine ⟨3541109106551909230184569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18885915234943515894317701 3541109106551909230184569)
                    ·
                      refine ⟨2655831829913931922638427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541109106551909230184569 2655831829913931922638427)
                      ·
                        rfl

theorem cell23_5172214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5172214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172214 prefixEnd_5172214 := by exact prefixLift 5172214
  have htrace : WordTrace (prefixWord ++ tailWord_5172214) baseStart_5172214 baseEnd_5172214 := by
    simpa [prefixWord, tailWord_5172214, baseEnd_5172214] using wordTrace_append hprefix tailTrace_5172214
  have hstable : (prefixWord ++ tailWord_5172214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172214).length < 2 ^ (prefixWord ++ tailWord_5172214).sum := by decide
  have hdescent : baseEnd_5172214 < baseStart_5172214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172233 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_5172233 : Nat := 118140960795 + 5172233 * 2 ^ 59
def prefixEnd_5172233 : Nat := 4983230072969 + 3 ^ 40 * 5172233 * 2
def baseEnd_5172233 : Nat := 885280528682122449433613

theorem tailTrace_5172233 : CollatzResearch.WordTrace tailWord_5172233 prefixEnd_5172233 885280528682122449433613 := by
  unfold tailWord_5172233
  simp only [CollatzResearch.WordTrace]
  refine ⟨188646835470890662914657353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125764556980593775276438235 188646835470890662914657353)
  ·
    refine ⟨141485126603167997185993015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188646835470890662914657353 141485126603167997185993015)
    ·
      refine ⟨212227689904751995778989523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141485126603167997185993015 212227689904751995778989523)
      ·
        refine ⟨318341534857127993668484285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212227689904751995778989523 318341534857127993668484285)
        ·
          refine ⟨119378075571422997625681607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318341534857127993668484285 119378075571422997625681607)
          ·
            refine ⟨179067113357134496438522411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119378075571422997625681607 179067113357134496438522411)
            ·
              refine ⟨268600670035701744657783617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179067113357134496438522411 268600670035701744657783617)
              ·
                refine ⟨201450502526776308493337713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268600670035701744657783617 201450502526776308493337713)
                ·
                  refine ⟨151087876895082231370003285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201450502526776308493337713 151087876895082231370003285)
                  ·
                    refine ⟨885280528682122449433613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151087876895082231370003285 885280528682122449433613)
                    ·
                      rfl

theorem cell23_5172233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_5172233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172233 prefixEnd_5172233 := by exact prefixLift 5172233
  have htrace : WordTrace (prefixWord ++ tailWord_5172233) baseStart_5172233 baseEnd_5172233 := by
    simpa [prefixWord, tailWord_5172233, baseEnd_5172233] using wordTrace_append hprefix tailTrace_5172233
  have hstable : (prefixWord ++ tailWord_5172233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172233).length < 2 ^ (prefixWord ++ tailWord_5172233).sum := by decide
  have hdescent : baseEnd_5172233 < baseStart_5172233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172284 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_5172284 : Nat := 118140960795 + 5172284 * 2 ^ 59
def prefixEnd_5172284 : Nat := 4983230072969 + 3 ^ 40 * 5172284 * 2
def baseEnd_5172284 : Nat := 885289257853248882921035

theorem tailTrace_5172284 : CollatzResearch.WordTrace tailWord_5172284 prefixEnd_5172284 885289257853248882921035 := by
  unfold tailWord_5172284
  simp only [CollatzResearch.WordTrace]
  refine ⟨94324347796852949312381953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125765797062470599083175937 94324347796852949312381953)
  ·
    refine ⟨70743260847639711984286465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94324347796852949312381953 70743260847639711984286465)
    ·
      refine ⟨53057445635729783988214849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70743260847639711984286465 53057445635729783988214849)
      ·
        refine ⟨39793084226797337991161137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53057445635729783988214849 39793084226797337991161137)
        ·
          refine ⟨29844813170098003493370853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39793084226797337991161137 29844813170098003493370853)
          ·
            refine ⟨5595902469393375655007035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29844813170098003493370853 5595902469393375655007035)
            ·
              refine ⟨8393853704090063482510553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595902469393375655007035 8393853704090063482510553)
              ·
                refine ⟨6295390278067547611882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8393853704090063482510553 6295390278067547611882915)
                ·
                  refine ⟨9443085417101321417824373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295390278067547611882915 9443085417101321417824373)
                  ·
                    refine ⟨885289257853248882921035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9443085417101321417824373 885289257853248882921035)
                    ·
                      rfl

theorem cell23_5172284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_5172284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172284 prefixEnd_5172284 := by exact prefixLift 5172284
  have htrace : WordTrace (prefixWord ++ tailWord_5172284) baseStart_5172284 baseEnd_5172284 := by
    simpa [prefixWord, tailWord_5172284, baseEnd_5172284] using wordTrace_append hprefix tailTrace_5172284
  have hstable : (prefixWord ++ tailWord_5172284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172284).length < 2 ^ (prefixWord ++ tailWord_5172284).sum := by decide
  have hdescent : baseEnd_5172284 < baseStart_5172284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172301 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5172301 : Nat := 118140960795 + 5172301 * 2 ^ 59
def prefixEnd_5172301 : Nat := 4983230072969 + 3 ^ 40 * 5172301 * 2
def baseEnd_5172301 : Nat := 885292167576957694083509

theorem tailTrace_5172301 : CollatzResearch.WordTrace tailWord_5172301 prefixEnd_5172301 885292167576957694083509 := by
  unfold tailWord_5172301
  simp only [CollatzResearch.WordTrace]
  refine ⟨188649315634644310528132757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125766210423096207018755171 188649315634644310528132757)
  ·
    refine ⟨8842936670373952056006223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188649315634644310528132757 8842936670373952056006223)
    ·
      refine ⟨13264405005560928084009335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8842936670373952056006223 13264405005560928084009335)
      ·
        refine ⟨19896607508341392126014003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13264405005560928084009335 19896607508341392126014003)
        ·
          refine ⟨29844911262512088189021005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19896607508341392126014003 29844911262512088189021005)
          ·
            refine ⟨11191841723442033070882877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29844911262512088189021005 11191841723442033070882877)
            ·
              refine ⟨4196940646290762401581079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11191841723442033070882877 4196940646290762401581079)
              ·
                refine ⟨6295410969436143602371619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4196940646290762401581079 6295410969436143602371619)
                ·
                  refine ⟨9443116454154215403557429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6295410969436143602371619 9443116454154215403557429)
                  ·
                    refine ⟨885292167576957694083509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9443116454154215403557429 885292167576957694083509)
                    ·
                      rfl

theorem cell23_5172301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5172301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172301 prefixEnd_5172301 := by exact prefixLift 5172301
  have htrace : WordTrace (prefixWord ++ tailWord_5172301) baseStart_5172301 baseEnd_5172301 := by
    simpa [prefixWord, tailWord_5172301, baseEnd_5172301] using wordTrace_append hprefix tailTrace_5172301
  have hstable : (prefixWord ++ tailWord_5172301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172301).length < 2 ^ (prefixWord ++ tailWord_5172301).sum := by decide
  have hdescent : baseEnd_5172301 < baseStart_5172301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172327 : List Nat := [1, 1, 5, 1, 1, 5, 1, 8]
def baseStart_5172327 : Nat := 118140960795 + 5172327 * 2 ^ 59
def prefixEnd_5172327 : Nat := 4983230072969 + 3 ^ 40 * 5172327 * 2
def baseEnd_5172327 : Nat := 98366290860292221500941

theorem tailTrace_5172327 : CollatzResearch.WordTrace tailWord_5172327 prefixEnd_5172327 98366290860292221500941 := by
  unfold tailWord_5172327
  simp only [CollatzResearch.WordTrace]
  refine ⟨188650263932550116968579235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125766842621700077979052823 188650263932550116968579235)
  ·
    refine ⟨282975395898825175452868853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188650263932550116968579235 282975395898825175452868853)
    ·
      refine ⟨26528943365514860198706455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 282975395898825175452868853 26528943365514860198706455)
      ·
        refine ⟨39793415048272290298059683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26528943365514860198706455 39793415048272290298059683)
        ·
          refine ⟨59690122572408435447089525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39793415048272290298059683 59690122572408435447089525)
          ·
            refine ⟨5595948991163290823164643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59690122572408435447089525 5595948991163290823164643)
            ·
              refine ⟨8393923486744936234746965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5595948991163290823164643 8393923486744936234746965)
              ·
                refine ⟨98366290860292221500941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8393923486744936234746965 98366290860292221500941)
                ·
                  rfl

theorem cell23_5172327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 8].length) (baseStart_5172327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172327 prefixEnd_5172327 := by exact prefixLift 5172327
  have htrace : WordTrace (prefixWord ++ tailWord_5172327) baseStart_5172327 baseEnd_5172327 := by
    simpa [prefixWord, tailWord_5172327, baseEnd_5172327] using wordTrace_append hprefix tailTrace_5172327
  have hstable : (prefixWord ++ tailWord_5172327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172327).length < 2 ^ (prefixWord ++ tailWord_5172327).sum := by decide
  have hdescent : baseEnd_5172327 < baseStart_5172327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172334 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_5172334 : Nat := 118140960795 + 5172334 * 2 ^ 59
def prefixEnd_5172334 : Nat := 4983230072969 + 3 ^ 40 * 5172334 * 2
def baseEnd_5172334 : Nat := 2655893447592471453137875

theorem tailTrace_5172334 : CollatzResearch.WordTrace tailWord_5172334 prefixEnd_5172334 2655893447592471453137875 := by
  unfold tailWord_5172334
  simp only [CollatzResearch.WordTrace]
  refine ⟨23581314905440594645510507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125767012829016504776056037 23581314905440594645510507)
  ·
    refine ⟨35371972358160891968265761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23581314905440594645510507 35371972358160891968265761)
    ·
      refine ⟨26528979268620668976199321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35371972358160891968265761 26528979268620668976199321)
      ·
        refine ⟨19896734451465501732149491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26528979268620668976199321 19896734451465501732149491)
        ·
          refine ⟨29845101677198252598224237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19896734451465501732149491 29845101677198252598224237)
          ·
            refine ⟨11191913128949344724334089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29845101677198252598224237 11191913128949344724334089)
            ·
              refine ⟨8393934846712008543250567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11191913128949344724334089 8393934846712008543250567)
              ·
                refine ⟨12590902270068012814875851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8393934846712008543250567 12590902270068012814875851)
                ·
                  refine ⟨18886353405102019222313777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12590902270068012814875851 18886353405102019222313777)
                  ·
                    refine ⟨14164765053826514416735333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18886353405102019222313777 14164765053826514416735333)
                    ·
                      refine ⟨2655893447592471453137875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14164765053826514416735333 2655893447592471453137875)
                      ·
                        rfl

theorem cell23_5172334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_5172334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172334 prefixEnd_5172334 := by exact prefixLift 5172334
  have htrace : WordTrace (prefixWord ++ tailWord_5172334) baseStart_5172334 baseEnd_5172334 := by
    simpa [prefixWord, tailWord_5172334, baseEnd_5172334] using wordTrace_append hprefix tailTrace_5172334
  have hstable : (prefixWord ++ tailWord_5172334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172334).length < 2 ^ (prefixWord ++ tailWord_5172334).sum := by decide
  have hdescent : baseEnd_5172334 < baseStart_5172334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172377 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 8, 2]
def baseStart_5172377 : Nat := 118140960795 + 5172377 * 2 ^ 59
def prefixEnd_5172377 : Nat := 4983230072969 + 3 ^ 40 * 5172377 * 2
def baseEnd_5172377 : Nat := 2655915527260614784900177

theorem tailTrace_5172377 : CollatzResearch.WordTrace tailWord_5172377 prefixEnd_5172377 2655915527260614784900177 := by
  unfold tailWord_5172377
  simp only [CollatzResearch.WordTrace]
  refine ⟨188652087582368975507899385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125768058388245983671932923 188652087582368975507899385)
  ·
    refine ⟨141489065686776731630924539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188652087582368975507899385 141489065686776731630924539)
    ·
      refine ⟨212233598530165097446386809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141489065686776731630924539 212233598530165097446386809)
      ·
        refine ⟨159175198897623823084790107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212233598530165097446386809 159175198897623823084790107)
        ·
          refine ⟨238762798346435734627185161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159175198897623823084790107 238762798346435734627185161)
          ·
            refine ⟨179072098759826800970388871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238762798346435734627185161 179072098759826800970388871)
            ·
              refine ⟨268608148139740201455583307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179072098759826800970388871 268608148139740201455583307)
              ·
                refine ⟨402912222209610302183374961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268608148139740201455583307 402912222209610302183374961)
                ·
                  refine ⟨302184166657207726637531221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402912222209610302183374961 302184166657207726637531221)
                  ·
                    refine ⟨3541220703014153046533569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 302184166657207726637531221 3541220703014153046533569)
                    ·
                      refine ⟨2655915527260614784900177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541220703014153046533569 2655915527260614784900177)
                      ·
                        rfl

theorem cell23_5172377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_5172377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172377 prefixEnd_5172377 := by exact prefixLift 5172377
  have htrace : WordTrace (prefixWord ++ tailWord_5172377) baseStart_5172377 baseEnd_5172377 := by
    simpa [prefixWord, tailWord_5172377, baseEnd_5172377] using wordTrace_append hprefix tailTrace_5172377
  have hstable : (prefixWord ++ tailWord_5172377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172377).length < 2 ^ (prefixWord ++ tailWord_5172377).sum := by decide
  have hdescent : baseEnd_5172377 < baseStart_5172377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172388 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_5172388 : Nat := 118140960795 + 5172388 * 2 ^ 59
def prefixEnd_5172388 : Nat := 4983230072969 + 3 ^ 40 * 5172388 * 2
def baseEnd_5172388 : Nat := 2655921175547814241862627

theorem tailTrace_5172388 : CollatzResearch.WordTrace tailWord_5172388 prefixEnd_5172388 2655921175547814241862627 := by
  unfold tailWord_5172388
  simp only [CollatzResearch.WordTrace]
  refine ⟨94326244392664562193274909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125768325856886082924366545 94326244392664562193274909)
  ·
    refine ⟨35372341647249210822478091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94326244392664562193274909 35372341647249210822478091)
    ·
      refine ⟨53058512470873816233717137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35372341647249210822478091 53058512470873816233717137)
      ·
        refine ⟨39793884353155362175287853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53058512470873816233717137 39793884353155362175287853)
        ·
          refine ⟨14922706632433260815732945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39793884353155362175287853 14922706632433260815732945)
          ·
            refine ⟨11192029974324945611799709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922706632433260815732945 11192029974324945611799709)
            ·
              refine ⟨4197011240371854604424891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11192029974324945611799709 4197011240371854604424891)
              ·
                refine ⟨6295516860557781906637337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197011240371854604424891 6295516860557781906637337)
                ·
                  refine ⟨4721637645418336429978003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6295516860557781906637337 4721637645418336429978003)
                  ·
                    refine ⟨7082456468127504644967005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721637645418336429978003 7082456468127504644967005)
                    ·
                      refine ⟨2655921175547814241862627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7082456468127504644967005 2655921175547814241862627)
                      ·
                        rfl

theorem cell23_5172388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_5172388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172388 prefixEnd_5172388 := by exact prefixLift 5172388
  have htrace : WordTrace (prefixWord ++ tailWord_5172388) baseStart_5172388 baseEnd_5172388 := by
    simpa [prefixWord, tailWord_5172388, baseEnd_5172388] using wordTrace_append hprefix tailTrace_5172388
  have hstable : (prefixWord ++ tailWord_5172388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172388).length < 2 ^ (prefixWord ++ tailWord_5172388).sum := by decide
  have hdescent : baseEnd_5172388 < baseStart_5172388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172406 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5172406 : Nat := 118140960795 + 5172406 * 2 ^ 59
def prefixEnd_5172406 : Nat := 4983230072969 + 3 ^ 40 * 5172406 * 2
def baseEnd_5172406 : Nat := 2655930418199595171437545

theorem tailTrace_5172406 : CollatzResearch.WordTrace tailWord_5172406 prefixEnd_5172406 2655930418199595171437545 := by
  unfold tailWord_5172406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790821581203994591294067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125768763532842608973803381 11790821581203994591294067)
  ·
    refine ⟨17686232371805991886941101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790821581203994591294067 17686232371805991886941101)
    ·
      refine ⟨6632337139427246957602913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17686232371805991886941101 6632337139427246957602913)
      ·
        refine ⟨4974252854570435218202185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6632337139427246957602913 4974252854570435218202185)
        ·
          refine ⟨3730689640927826413651639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974252854570435218202185 3730689640927826413651639)
          ·
            refine ⟨5596034461391739620477459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3730689640927826413651639 5596034461391739620477459)
            ·
              refine ⟨8394051692087609430716189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596034461391739620477459 8394051692087609430716189)
              ·
                refine ⟨3147769384532853536518571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8394051692087609430716189 3147769384532853536518571)
                ·
                  refine ⟨4721654076799280304777857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147769384532853536518571 4721654076799280304777857)
                  ·
                    refine ⟨3541240557599460228583393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721654076799280304777857 3541240557599460228583393)
                    ·
                      refine ⟨2655930418199595171437545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541240557599460228583393 2655930418199595171437545)
                      ·
                        rfl

theorem cell23_5172406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5172406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172406 prefixEnd_5172406 := by exact prefixLift 5172406
  have htrace : WordTrace (prefixWord ++ tailWord_5172406) baseStart_5172406 baseEnd_5172406 := by
    simpa [prefixWord, tailWord_5172406, baseEnd_5172406] using wordTrace_append hprefix tailTrace_5172406
  have hstable : (prefixWord ++ tailWord_5172406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172406).length < 2 ^ (prefixWord ++ tailWord_5172406).sum := by decide
  have hdescent : baseEnd_5172406 < baseStart_5172406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172414 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5172414 : Nat := 118140960795 + 5172414 * 2 ^ 59
def prefixEnd_5172414 : Nat := 4983230072969 + 3 ^ 40 * 5172414 * 2
def baseEnd_5172414 : Nat := 2655934526044831140137507

theorem tailTrace_5172414 : CollatzResearch.WordTrace tailWord_5172414 prefixEnd_5172414 2655934526044831140137507 := by
  unfold tailWord_5172414
  simp only [CollatzResearch.WordTrace]
  refine ⟨23581679635404366353374537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125768958055489953884664197 23581679635404366353374537)
  ·
    refine ⟨17686259726553274765030903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23581679635404366353374537 17686259726553274765030903)
    ·
      refine ⟨26529389589829912147546355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17686259726553274765030903 26529389589829912147546355)
      ·
        refine ⟨39794084384744868221319533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26529389589829912147546355 39794084384744868221319533)
        ·
          refine ⟨14922781644279325582994825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39794084384744868221319533 14922781644279325582994825)
          ·
            refine ⟨11192086233209494187246119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922781644279325582994825 11192086233209494187246119)
            ·
              refine ⟨16788129349814241280869179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192086233209494187246119 16788129349814241280869179)
              ·
                refine ⟨25182194024721361921303769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16788129349814241280869179 25182194024721361921303769)
                ·
                  refine ⟨18886645518541021440977827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25182194024721361921303769 18886645518541021440977827)
                  ·
                    refine ⟨28329968277811532161466741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18886645518541021440977827 28329968277811532161466741)
                    ·
                      refine ⟨2655934526044831140137507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28329968277811532161466741 2655934526044831140137507)
                      ·
                        rfl

theorem cell23_5172414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5172414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172414 prefixEnd_5172414 := by exact prefixLift 5172414
  have htrace : WordTrace (prefixWord ++ tailWord_5172414) baseStart_5172414 baseEnd_5172414 := by
    simpa [prefixWord, tailWord_5172414, baseEnd_5172414] using wordTrace_append hprefix tailTrace_5172414
  have hstable : (prefixWord ++ tailWord_5172414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172414).length < 2 ^ (prefixWord ++ tailWord_5172414).sum := by decide
  have hdescent : baseEnd_5172414 < baseStart_5172414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172427 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3]
def baseStart_5172427 : Nat := 118140960795 + 5172427 * 2 ^ 59
def prefixEnd_5172427 : Nat := 4983230072969 + 3 ^ 40 * 5172427 * 2
def baseEnd_5172427 : Nat := 2655941201293339589274947

theorem tailTrace_5172427 : CollatzResearch.WordTrace tailWord_5172427 prefixEnd_5172427 2655941201293339589274947 := by
  unfold tailWord_5172427
  simp only [CollatzResearch.WordTrace]
  refine ⟨188653911232187834047219535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125769274154791889364813023 188653911232187834047219535)
  ·
    refine ⟨282980866848281751070829303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188653911232187834047219535 282980866848281751070829303)
    ·
      refine ⟨424471300272422626606243955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282980866848281751070829303 424471300272422626606243955)
      ·
        refine ⟨636706950408633939909365933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424471300272422626606243955 636706950408633939909365933)
        ·
          refine ⟨238765106403237727466012225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636706950408633939909365933 238765106403237727466012225)
          ·
            refine ⟨179073829802428295599509169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238765106403237727466012225 179073829802428295599509169)
            ·
              refine ⟨134305372351821221699631877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179073829802428295599509169 134305372351821221699631877)
              ·
                refine ⟨25182257315966479068680977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134305372351821221699631877 25182257315966479068680977)
                ·
                  refine ⟨18886692986974859301510733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25182257315966479068680977 18886692986974859301510733)
                  ·
                    refine ⟨7082509870115572238066525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18886692986974859301510733 7082509870115572238066525)
                    ·
                      refine ⟨2655941201293339589274947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7082509870115572238066525 2655941201293339589274947)
                      ·
                        rfl

theorem cell23_5172427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 3].length) (baseStart_5172427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172427 prefixEnd_5172427 := by exact prefixLift 5172427
  have htrace : WordTrace (prefixWord ++ tailWord_5172427) baseStart_5172427 baseEnd_5172427 := by
    simpa [prefixWord, tailWord_5172427, baseEnd_5172427] using wordTrace_append hprefix tailTrace_5172427
  have hstable : (prefixWord ++ tailWord_5172427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172427).length < 2 ^ (prefixWord ++ tailWord_5172427).sum := by decide
  have hdescent : baseEnd_5172427 < baseStart_5172427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172445 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5172445 : Nat := 118140960795 + 5172445 * 2 ^ 59
def prefixEnd_5172445 : Nat := 4983230072969 + 3 ^ 40 * 5172445 * 2
def baseEnd_5172445 : Nat := 2655950443945120518849865

theorem tailTrace_5172445 : CollatzResearch.WordTrace tailWord_5172445 prefixEnd_5172445 2655950443945120518849865 := by
  unfold tailWord_5172445
  simp only [CollatzResearch.WordTrace]
  refine ⟨188654567746122623121374789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125769711830748415414249859 188654567746122623121374789)
  ·
    refine ⟨35372731452397991835257773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188654567746122623121374789 35372731452397991835257773)
    ·
      refine ⟨13264774294649246938221665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35372731452397991835257773 13264774294649246938221665)
      ·
        refine ⟨9948580720986935203666249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13264774294649246938221665 9948580720986935203666249)
        ·
          refine ⟨7461435540740201402749687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9948580720986935203666249 7461435540740201402749687)
          ·
            refine ⟨11192153311110302104124531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461435540740201402749687 11192153311110302104124531)
            ·
              refine ⟨16788229966665453156186797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192153311110302104124531 16788229966665453156186797)
              ·
                refine ⟨6295586237499544933570049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16788229966665453156186797 6295586237499544933570049)
                ·
                  refine ⟨4721689678124658700177537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6295586237499544933570049 4721689678124658700177537)
                  ·
                    refine ⟨3541267258593494025133153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721689678124658700177537 3541267258593494025133153)
                    ·
                      refine ⟨2655950443945120518849865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541267258593494025133153 2655950443945120518849865)
                      ·
                        rfl

theorem cell23_5172445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5172445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172445 prefixEnd_5172445 := by exact prefixLift 5172445
  have htrace : WordTrace (prefixWord ++ tailWord_5172445) baseStart_5172445 baseEnd_5172445 := by
    simpa [prefixWord, tailWord_5172445, baseEnd_5172445] using wordTrace_append hprefix tailTrace_5172445
  have hstable : (prefixWord ++ tailWord_5172445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172445).length < 2 ^ (prefixWord ++ tailWord_5172445).sum := by decide
  have hdescent : baseEnd_5172445 < baseStart_5172445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172511 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 3, 4]
def baseStart_5172511 : Nat := 118140960795 + 5172511 * 2 ^ 59
def prefixEnd_5172511 : Nat := 4983230072969 + 3 ^ 40 * 5172511 * 2
def baseEnd_5172511 : Nat := 885328111222772420208187

theorem tailTrace_5172511 : CollatzResearch.WordTrace tailWord_5172511 prefixEnd_5172511 885328111222772420208187 := by
  unfold tailWord_5172511
  simp only [CollatzResearch.WordTrace]
  refine ⟨188656974963883516393277387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125771316642589010928851591 188656974963883516393277387)
  ·
    refine ⟨282985462445825274589916081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188656974963883516393277387 282985462445825274589916081)
    ·
      refine ⟨212239096834368955942437061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282985462445825274589916081 212239096834368955942437061)
      ·
        refine ⟨39794830656444179239206949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212239096834368955942437061 39794830656444179239206949)
        ·
          refine ⟨7461530748083283607351303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39794830656444179239206949 7461530748083283607351303)
          ·
            refine ⟨11192296122124925411026955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461530748083283607351303 11192296122124925411026955)
            ·
              refine ⟨16788444183187388116540433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192296122124925411026955 16788444183187388116540433)
              ·
                refine ⟨12591333137390541087405325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16788444183187388116540433 12591333137390541087405325)
                ·
                  refine ⟨4721749926521452907776997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12591333137390541087405325 4721749926521452907776997)
                  ·
                    refine ⟨885328111222772420208187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4721749926521452907776997 885328111222772420208187)
                    ·
                      rfl

theorem cell23_5172511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_5172511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172511 prefixEnd_5172511 := by exact prefixLift 5172511
  have htrace : WordTrace (prefixWord ++ tailWord_5172511) baseStart_5172511 baseEnd_5172511 := by
    simpa [prefixWord, tailWord_5172511, baseEnd_5172511] using wordTrace_append hprefix tailTrace_5172511
  have hstable : (prefixWord ++ tailWord_5172511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172511).length < 2 ^ (prefixWord ++ tailWord_5172511).sum := by decide
  have hdescent : baseEnd_5172511 < baseStart_5172511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172541 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 8]
def baseStart_5172541 : Nat := 118140960795 + 5172541 * 2 ^ 59
def prefixEnd_5172541 : Nat := 4983230072969 + 3 ^ 40 * 5172541 * 2
def baseEnd_5172541 : Nat := 295111082009772460361047

theorem tailTrace_5172541 : CollatzResearch.WordTrace tailWord_5172541 prefixEnd_5172541 295111082009772460361047 := by
  unfold tailWord_5172541
  simp only [CollatzResearch.WordTrace]
  refine ⟨188658069153774831516869477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125772046102516554344579651 188658069153774831516869477)
  ·
    refine ⟨35373387966332780909413027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188658069153774831516869477 35373387966332780909413027)
    ·
      refine ⟨53060081949499171364119541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35373387966332780909413027 53060081949499171364119541)
      ·
        refine ⟨4974382682765547315386207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53060081949499171364119541 4974382682765547315386207)
        ·
          refine ⟨7461574024148320973079311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4974382682765547315386207 7461574024148320973079311)
          ·
            refine ⟨11192361036222481459618967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461574024148320973079311 11192361036222481459618967)
            ·
              refine ⟨16788541554333722189428451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192361036222481459618967 16788541554333722189428451)
              ·
                refine ⟨25182812331500583284142677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16788541554333722189428451 25182812331500583284142677)
                ·
                  refine ⟨295111082009772460361047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25182812331500583284142677 295111082009772460361047)
                  ·
                    rfl

theorem cell23_5172541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_5172541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172541 prefixEnd_5172541 := by exact prefixLift 5172541
  have htrace : WordTrace (prefixWord ++ tailWord_5172541) baseStart_5172541 baseEnd_5172541 := by
    simpa [prefixWord, tailWord_5172541, baseEnd_5172541] using wordTrace_append hprefix tailTrace_5172541
  have hstable : (prefixWord ++ tailWord_5172541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172541).length < 2 ^ (prefixWord ++ tailWord_5172541).sum := by decide
  have hdescent : baseEnd_5172541 < baseStart_5172541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172551 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_5172551 : Nat := 118140960795 + 5172551 * 2 ^ 59
def prefixEnd_5172551 : Nat := 4983230072969 + 3 ^ 40 * 5172551 * 2
def baseEnd_5172551 : Nat := 2656004872894497104124377

theorem tailTrace_5172551 : CollatzResearch.WordTrace tailWord_5172551 prefixEnd_5172551 2656004872894497104124377 := by
  unfold tailWord_5172551
  simp only [CollatzResearch.WordTrace]
  refine ⟨188658433883738603224733507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125772289255825735483155671 188658433883738603224733507)
  ·
    refine ⟨282987650825607904837100261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188658433883738603224733507 282987650825607904837100261)
    ·
      refine ⟨53060184529801482156956299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282987650825607904837100261 53060184529801482156956299)
      ·
        refine ⟨79590276794702223235434449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53060184529801482156956299 79590276794702223235434449)
        ·
          refine ⟨59692707596026667426575837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79590276794702223235434449 59692707596026667426575837)
          ·
            refine ⟨22384765348510000284965939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59692707596026667426575837 22384765348510000284965939)
            ·
              refine ⟨33577148022765000427448909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22384765348510000284965939 33577148022765000427448909)
              ·
                refine ⟨12591430508536875160293341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33577148022765000427448909 12591430508536875160293341)
                ·
                  refine ⟨4721786440701328185110003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12591430508536875160293341 4721786440701328185110003)
                  ·
                    refine ⟨7082679661051992277665005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721786440701328185110003 7082679661051992277665005)
                    ·
                      refine ⟨2656004872894497104124377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7082679661051992277665005 2656004872894497104124377)
                      ·
                        rfl

theorem cell23_5172551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_5172551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172551 prefixEnd_5172551 := by exact prefixLift 5172551
  have htrace : WordTrace (prefixWord ++ tailWord_5172551) baseStart_5172551 baseEnd_5172551 := by
    simpa [prefixWord, tailWord_5172551, baseEnd_5172551] using wordTrace_append hprefix tailTrace_5172551
  have hstable : (prefixWord ++ tailWord_5172551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172551).length < 2 ^ (prefixWord ++ tailWord_5172551).sum := by decide
  have hdescent : baseEnd_5172551 < baseStart_5172551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172578 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5172578 : Nat := 118140960795 + 5172578 * 2 ^ 59
def prefixEnd_5172578 : Nat := 4983230072969 + 3 ^ 40 * 5172578 * 2
def baseEnd_5172578 : Nat := 2656018736872168498486753

theorem tailTrace_5172578 : CollatzResearch.WordTrace tailWord_5172578 prefixEnd_5172578 2656018736872168498486753 := by
  unfold tailWord_5172578
  simp only [CollatzResearch.WordTrace]
  refine ⟨47164854663660196708991597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125772945769760524557310925 47164854663660196708991597)
  ·
    refine ⟨17686820498872573765871849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47164854663660196708991597 17686820498872573765871849)
    ·
      refine ⟨13265115374154430324403887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17686820498872573765871849 13265115374154430324403887)
      ·
        refine ⟨19897673061231645486605831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265115374154430324403887 19897673061231645486605831)
        ·
          refine ⟨29846509591847468229908747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19897673061231645486605831 29846509591847468229908747)
          ·
            refine ⟨44769764387771202344863121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29846509591847468229908747 44769764387771202344863121)
            ·
              refine ⟨33577323290828401758647341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44769764387771202344863121 33577323290828401758647341)
              ·
                refine ⟨12591496234060650659492753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33577323290828401758647341 12591496234060650659492753)
                ·
                  refine ⟨9443622175545487994619565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12591496234060650659492753 9443622175545487994619565)
                  ·
                    refine ⟨3541358315829557997982337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9443622175545487994619565 3541358315829557997982337)
                    ·
                      refine ⟨2656018736872168498486753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541358315829557997982337 2656018736872168498486753)
                      ·
                        rfl

theorem cell23_5172578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5172578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172578 prefixEnd_5172578 := by exact prefixLift 5172578
  have htrace : WordTrace (prefixWord ++ tailWord_5172578) baseStart_5172578 baseEnd_5172578 := by
    simpa [prefixWord, tailWord_5172578, baseEnd_5172578] using wordTrace_append hprefix tailTrace_5172578
  have hstable : (prefixWord ++ tailWord_5172578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172578).length < 2 ^ (prefixWord ++ tailWord_5172578).sum := by decide
  have hdescent : baseEnd_5172578 < baseStart_5172578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172587 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_5172587 : Nat := 118140960795 + 5172587 * 2 ^ 59
def prefixEnd_5172587 : Nat := 4983230072969 + 3 ^ 40 * 5172587 * 2
def baseEnd_5172587 : Nat := 2656023358198058963274211

theorem tailTrace_5172587 : CollatzResearch.WordTrace tailWord_5172587 prefixEnd_5172587 2656023358198058963274211 := by
  unfold tailWord_5172587
  simp only [CollatzResearch.WordTrace]
  refine ⟨188659746911608181373044015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125773164607738787582029343 188659746911608181373044015)
  ·
    refine ⟨282989620367412272059566023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188659746911608181373044015 282989620367412272059566023)
    ·
      refine ⟨424484430551118408089349035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282989620367412272059566023 424484430551118408089349035)
      ·
        refine ⟨636726645826677612134023553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424484430551118408089349035 636726645826677612134023553)
        ·
          refine ⟨477544984370008209100517665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636726645826677612134023553 477544984370008209100517665)
          ·
            refine ⟨358158738277506156825388249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477544984370008209100517665 358158738277506156825388249)
            ·
              refine ⟨268619053708129617619041187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358158738277506156825388249 268619053708129617619041187)
              ·
                refine ⟨402928580562194426428561781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268619053708129617619041187 402928580562194426428561781)
                ·
                  refine ⟨37774554427705727477677667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402928580562194426428561781 37774554427705727477677667)
                  ·
                    refine ⟨56661831641558591216516501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37774554427705727477677667 56661831641558591216516501)
                    ·
                      refine ⟨2656023358198058963274211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56661831641558591216516501 2656023358198058963274211)
                      ·
                        rfl

theorem cell23_5172587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_5172587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172587 prefixEnd_5172587 := by exact prefixLift 5172587
  have htrace : WordTrace (prefixWord ++ tailWord_5172587) baseStart_5172587 baseEnd_5172587 := by
    simpa [prefixWord, tailWord_5172587, baseEnd_5172587] using wordTrace_append hprefix tailTrace_5172587
  have hstable : (prefixWord ++ tailWord_5172587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172587).length < 2 ^ (prefixWord ++ tailWord_5172587).sum := by decide
  have hdescent : baseEnd_5172587 < baseStart_5172587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172607 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_5172607 : Nat := 118140960795 + 5172607 * 2 ^ 59
def prefixEnd_5172607 : Nat := 4983230072969 + 3 ^ 40 * 5172607 * 2
def baseEnd_5172607 : Nat := 2656033627811148885024119

theorem tailTrace_5172607 : CollatzResearch.WordTrace tailWord_5172607 prefixEnd_5172607 2656033627811148885024119 := by
  unfold tailWord_5172607
  simp only [CollatzResearch.WordTrace]
  refine ⟨188660476371535724788772075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125773650914357149859181383 188660476371535724788772075)
  ·
    refine ⟨282990714557303587183158113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188660476371535724788772075 282990714557303587183158113)
    ·
      refine ⟨212243035917977690387368585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282990714557303587183158113 212243035917977690387368585)
      ·
        refine ⟨159182276938483267790526439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212243035917977690387368585 159182276938483267790526439)
        ·
          refine ⟨238773415407724901685789659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159182276938483267790526439 238773415407724901685789659)
          ·
            refine ⟨358160123111587352528684489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238773415407724901685789659 358160123111587352528684489)
            ·
              refine ⟨268620092333690514396513367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358160123111587352528684489 268620092333690514396513367)
              ·
                refine ⟨402930138500535771594770051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268620092333690514396513367 402930138500535771594770051)
                ·
                  refine ⟨604395207750803657392155077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402930138500535771594770051 604395207750803657392155077)
                  ·
                    refine ⟨113324101453275685761029077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 604395207750803657392155077 113324101453275685761029077)
                    ·
                      refine ⟨2656033627811148885024119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113324101453275685761029077 2656033627811148885024119)
                      ·
                        rfl

theorem cell23_5172607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_5172607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172607 prefixEnd_5172607 := by exact prefixLift 5172607
  have htrace : WordTrace (prefixWord ++ tailWord_5172607) baseStart_5172607 baseEnd_5172607 := by
    simpa [prefixWord, tailWord_5172607, baseEnd_5172607] using wordTrace_append hprefix tailTrace_5172607
  have hstable : (prefixWord ++ tailWord_5172607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172607).length < 2 ^ (prefixWord ++ tailWord_5172607).sum := by decide
  have hdescent : baseEnd_5172607 < baseStart_5172607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
