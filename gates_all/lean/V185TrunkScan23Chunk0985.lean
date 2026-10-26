import V185TrunkScan23Chunk0984

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5831588 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_5831588 : Nat := 118140960795 + 5831588 * 2 ^ 59
def prefixEnd_5831588 : Nat := 4983230072969 + 3 ^ 40 * 5831588 * 2
def baseEnd_5831588 : Nat := 2994407622991635118831021

theorem tailTrace_5831588 : CollatzResearch.WordTrace tailWord_5831588 prefixEnd_5831588 2994407622991635118831021 := by
  unfold tailWord_5831588
  simp only [CollatzResearch.WordTrace]
  refine ⟨106347743998580053391703709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141796991998106737855604945 106347743998580053391703709)
  ·
    refine ⟨39880403999467520021888891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106347743998580053391703709 39880403999467520021888891)
    ·
      refine ⟨59820605999201280032833337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39880403999467520021888891 59820605999201280032833337)
      ·
        refine ⟨44865454499400960024625003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59820605999201280032833337 44865454499400960024625003)
        ·
          refine ⟨67298181749101440036937505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44865454499400960024625003 67298181749101440036937505)
          ·
            refine ⟨50473636311826080027703129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67298181749101440036937505 50473636311826080027703129)
            ·
              refine ⟨37855227233869560020777347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50473636311826080027703129 37855227233869560020777347)
              ·
                refine ⟨56782840850804340031166021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37855227233869560020777347 56782840850804340031166021)
                ·
                  refine ⟨10646782659525813755843629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56782840850804340031166021 10646782659525813755843629)
                  ·
                    refine ⟨3992543497322180158441361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10646782659525813755843629 3992543497322180158441361)
                    ·
                      refine ⟨2994407622991635118831021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992543497322180158441361 2994407622991635118831021)
                      ·
                        rfl

theorem cell23_5831588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_5831588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831588 prefixEnd_5831588 := by exact prefixLift 5831588
  have htrace : WordTrace (prefixWord ++ tailWord_5831588) baseStart_5831588 baseEnd_5831588 := by
    simpa [prefixWord, tailWord_5831588, baseEnd_5831588] using wordTrace_append hprefix tailTrace_5831588
  have hstable : (prefixWord ++ tailWord_5831588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831588).length < 2 ^ (prefixWord ++ tailWord_5831588).sum := by decide
  have hdescent : baseEnd_5831588 < baseStart_5831588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831621 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_5831621 : Nat := 118140960795 + 5831621 * 2 ^ 59
def prefixEnd_5831621 : Nat := 4983230072969 + 3 ^ 40 * 5831621 * 2
def baseEnd_5831621 : Nat := 2994424567853233489718369

theorem tailTrace_5831621 : CollatzResearch.WordTrace tailWord_5831621 prefixEnd_5831621 2994424567853233489718369 := by
  unfold tailWord_5831621
  simp only [CollatzResearch.WordTrace]
  refine ⟨212696691606040553419358717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141797794404027035612905811 212696691606040553419358717)
  ·
    refine ⟨79761259352265207532259519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212696691606040553419358717 79761259352265207532259519)
    ·
      refine ⟨119641889028397811298389279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79761259352265207532259519 119641889028397811298389279)
      ·
        refine ⟨179462833542596716947583919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119641889028397811298389279 179462833542596716947583919)
        ·
          refine ⟨269194250313895075421375879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179462833542596716947583919 269194250313895075421375879)
          ·
            refine ⟨403791375470842613132063819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269194250313895075421375879 403791375470842613132063819)
            ·
              refine ⟨605687063206263919698095729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403791375470842613132063819 605687063206263919698095729)
              ·
                refine ⟨454265297404697939773571797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605687063206263919698095729 454265297404697939773571797)
                ·
                  refine ⟨10646842907922607963443089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 454265297404697939773571797 10646842907922607963443089)
                  ·
                    refine ⟨7985132180941955972582317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10646842907922607963443089 7985132180941955972582317)
                    ·
                      refine ⟨2994424567853233489718369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7985132180941955972582317 2994424567853233489718369)
                      ·
                        rfl

theorem cell23_5831621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_5831621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831621 prefixEnd_5831621 := by exact prefixLift 5831621
  have htrace : WordTrace (prefixWord ++ tailWord_5831621) baseStart_5831621 baseEnd_5831621 := by
    simpa [prefixWord, tailWord_5831621, baseEnd_5831621] using wordTrace_append hprefix tailTrace_5831621
  have hstable : (prefixWord ++ tailWord_5831621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831621).length < 2 ^ (prefixWord ++ tailWord_5831621).sum := by decide
  have hdescent : baseEnd_5831621 < baseStart_5831621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831641 : List Nat := [1, 2, 1, 2, 5, 3, 9]
def baseStart_5831641 : Nat := 118140960795 + 5831641 * 2 ^ 59
def prefixEnd_5831641 : Nat := 4983230072969 + 3 ^ 40 * 5831641 * 2
def baseEnd_5831641 : Nat := 36968331326744733474917

theorem tailTrace_5831641 : CollatzResearch.WordTrace tailWord_5831641 prefixEnd_5831641 36968331326744733474917 := by
  unfold tailWord_5831641
  simp only [CollatzResearch.WordTrace]
  refine ⟨212697421065968096835086777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141798280710645397890057851 212697421065968096835086777)
  ·
    refine ⟨159523065799476072626315083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212697421065968096835086777 159523065799476072626315083)
    ·
      refine ⟨239284598699214108939472625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159523065799476072626315083 239284598699214108939472625)
      ·
        refine ⟨179463449024410581704604469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239284598699214108939472625 179463449024410581704604469)
        ·
          refine ⟨16824698346038492034806669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179463449024410581704604469 16824698346038492034806669)
          ·
            refine ⟨6309261879764434513052501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16824698346038492034806669 6309261879764434513052501)
            ·
              refine ⟨36968331326744733474917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6309261879764434513052501 36968331326744733474917)
              ·
                rfl

theorem cell23_5831641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 9].length) (baseStart_5831641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831641 prefixEnd_5831641 := by exact prefixLift 5831641
  have htrace : WordTrace (prefixWord ++ tailWord_5831641) baseStart_5831641 baseEnd_5831641 := by
    simpa [prefixWord, tailWord_5831641, baseEnd_5831641] using wordTrace_append hprefix tailTrace_5831641
  have hstable : (prefixWord ++ tailWord_5831641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831641).length < 2 ^ (prefixWord ++ tailWord_5831641).sum := by decide
  have hdescent : baseEnd_5831641 < baseStart_5831641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831669 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5831669 : Nat := 118140960795 + 5831669 * 2 ^ 59
def prefixEnd_5831669 : Nat := 4983230072969 + 3 ^ 40 * 5831669 * 2
def baseEnd_5831669 : Nat := 2994449214924649301918149

theorem tailTrace_5831669 : CollatzResearch.WordTrace tailWord_5831669 prefixEnd_5831669 2994449214924649301918149 := by
  unfold tailWord_5831669
  simp only [CollatzResearch.WordTrace]
  refine ⟨212698442309866657617106061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141798961539911105078070707 212698442309866657617106061)
  ·
    refine ⟨79761915866199996606414773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212698442309866657617106061 79761915866199996606414773)
    ·
      refine ⟨7477679612456249681851385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79761915866199996606414773 7477679612456249681851385)
      ·
        refine ⟨5608259709342187261388539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7477679612456249681851385 5608259709342187261388539)
        ·
          refine ⟨8412389564013280892082809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608259709342187261388539 8412389564013280892082809)
          ·
            refine ⟨6309292173009960669062107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8412389564013280892082809 6309292173009960669062107)
            ·
              refine ⟨9463938259514941003593161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309292173009960669062107 9463938259514941003593161)
              ·
                refine ⟨7097953694636205752694871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463938259514941003593161 7097953694636205752694871)
                ·
                  refine ⟨10646930541954308629042307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097953694636205752694871 10646930541954308629042307)
                  ·
                    refine ⟨15970395812931462943563461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10646930541954308629042307 15970395812931462943563461)
                    ·
                      refine ⟨2994449214924649301918149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15970395812931462943563461 2994449214924649301918149)
                      ·
                        rfl

theorem cell23_5831669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5831669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831669 prefixEnd_5831669 := by exact prefixLift 5831669
  have htrace : WordTrace (prefixWord ++ tailWord_5831669) baseStart_5831669 baseEnd_5831669 := by
    simpa [prefixWord, tailWord_5831669, baseEnd_5831669] using wordTrace_append hprefix tailTrace_5831669
  have hstable : (prefixWord ++ tailWord_5831669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831669).length < 2 ^ (prefixWord ++ tailWord_5831669).sum := by decide
  have hdescent : baseEnd_5831669 < baseStart_5831669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831682 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5831682 : Nat := 118140960795 + 5831682 * 2 ^ 59
def prefixEnd_5831682 : Nat := 4983230072969 + 3 ^ 40 * 5831682 * 2
def baseEnd_5831682 : Nat := 2994455890173157751055589

theorem tailTrace_5831682 : CollatzResearch.WordTrace tailWord_5831682 prefixEnd_5831682 2994455890173157751055589 := by
  unfold tailWord_5831682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53174729114704890209332325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141799277639213040558219533 53174729114704890209332325)
  ·
    refine ⟨9970261709007166914249811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53174729114704890209332325 9970261709007166914249811)
    ·
      refine ⟨14955392563510750371374717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9970261709007166914249811 14955392563510750371374717)
      ·
        refine ⟨5608272211316531389265519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14955392563510750371374717 5608272211316531389265519)
        ·
          refine ⟨8412408316974797083898279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608272211316531389265519 8412408316974797083898279)
          ·
            refine ⟨12618612475462195625847419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412408316974797083898279 12618612475462195625847419)
            ·
              refine ⟨18927918713193293438771129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12618612475462195625847419 18927918713193293438771129)
              ·
                refine ⟨14195939034894970079078347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18927918713193293438771129 14195939034894970079078347)
                ·
                  refine ⟨21293908552342455118617521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14195939034894970079078347 21293908552342455118617521)
                  ·
                    refine ⟨15970431414256841338963141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21293908552342455118617521 15970431414256841338963141)
                    ·
                      refine ⟨2994455890173157751055589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15970431414256841338963141 2994455890173157751055589)
                      ·
                        rfl

theorem cell23_5831682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5831682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831682 prefixEnd_5831682 := by exact prefixLift 5831682
  have htrace : WordTrace (prefixWord ++ tailWord_5831682) baseStart_5831682 baseEnd_5831682 := by
    simpa [prefixWord, tailWord_5831682, baseEnd_5831682] using wordTrace_append hprefix tailTrace_5831682
  have hstable : (prefixWord ++ tailWord_5831682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831682).length < 2 ^ (prefixWord ++ tailWord_5831682).sum := by decide
  have hdescent : baseEnd_5831682 < baseStart_5831682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831742 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5831742 : Nat := 118140960795 + 5831742 * 2 ^ 59
def prefixEnd_5831742 : Nat := 4983230072969 + 3 ^ 40 * 5831742 * 2
def baseEnd_5831742 : Nat := 2994486699012427516305313

theorem tailTrace_5831742 : CollatzResearch.WordTrace tailWord_5831742 prefixEnd_5831742 2994486699012427516305313 := by
  unfold tailWord_5831742
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587638104825273885564185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141800736559068127389675653 26587638104825273885564185)
  ·
    refine ⟨19940728578618955414173139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26587638104825273885564185 19940728578618955414173139)
    ·
      refine ⟨29911092867928433121259709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19940728578618955414173139 29911092867928433121259709)
      ·
        refine ⟨11216659825473162420472391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29911092867928433121259709 11216659825473162420472391)
        ·
          refine ⟨16824989738209743630708587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216659825473162420472391 16824989738209743630708587)
          ·
            refine ⟨25237484607314615446062881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16824989738209743630708587 25237484607314615446062881)
            ·
              refine ⟨18928113455485961584547161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25237484607314615446062881 18928113455485961584547161)
              ·
                refine ⟨14196085091614471188410371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18928113455485961584547161 14196085091614471188410371)
                ·
                  refine ⟨21294127637421706782615557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14196085091614471188410371 21294127637421706782615557)
                  ·
                    refine ⟨3992648932016570021740417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21294127637421706782615557 3992648932016570021740417)
                    ·
                      refine ⟨2994486699012427516305313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992648932016570021740417 2994486699012427516305313)
                      ·
                        rfl

theorem cell23_5831742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5831742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831742 prefixEnd_5831742 := by exact prefixLift 5831742
  have htrace : WordTrace (prefixWord ++ tailWord_5831742) baseStart_5831742 baseEnd_5831742 := by
    simpa [prefixWord, tailWord_5831742, baseEnd_5831742] using wordTrace_append hprefix tailTrace_5831742
  have hstable : (prefixWord ++ tailWord_5831742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831742).length < 2 ^ (prefixWord ++ tailWord_5831742).sum := by decide
  have hdescent : baseEnd_5831742 < baseStart_5831742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831758 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_5831758 : Nat := 118140960795 + 5831758 * 2 ^ 59
def prefixEnd_5831758 : Nat := 4983230072969 + 3 ^ 40 * 5831758 * 2
def baseEnd_5831758 : Nat := 2994494914702899453705239

theorem tailTrace_5831758 : CollatzResearch.WordTrace tailWord_5831758 prefixEnd_5831758 2994494914702899453705239 := by
  unfold tailWord_5831758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587711050818028227136991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141801125604362817211397285 26587711050818028227136991)
  ·
    refine ⟨39881566576227042340705487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26587711050818028227136991 39881566576227042340705487)
    ·
      refine ⟨59822349864340563511058231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39881566576227042340705487 59822349864340563511058231)
      ·
        refine ⟨89733524796510845266587347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59822349864340563511058231 89733524796510845266587347)
        ·
          refine ⟨134600287194766267899881021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89733524796510845266587347 134600287194766267899881021)
          ·
            refine ⟨50475107698037350462455383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134600287194766267899881021 50475107698037350462455383)
            ·
              refine ⟨75712661547056025693683075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50475107698037350462455383 75712661547056025693683075)
              ·
                refine ⟨113568992320584038540524613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75712661547056025693683075 113568992320584038540524613)
                ·
                  refine ⟨21294186060109507226348365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113568992320584038540524613 21294186060109507226348365)
                  ·
                    refine ⟨7985319772541065209880637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21294186060109507226348365 7985319772541065209880637)
                    ·
                      refine ⟨2994494914702899453705239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7985319772541065209880637 2994494914702899453705239)
                      ·
                        rfl

theorem cell23_5831758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_5831758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831758 prefixEnd_5831758 := by exact prefixLift 5831758
  have htrace : WordTrace (prefixWord ++ tailWord_5831758) baseStart_5831758 baseEnd_5831758 := by
    simpa [prefixWord, tailWord_5831758, baseEnd_5831758] using wordTrace_append hprefix tailTrace_5831758
  have hstable : (prefixWord ++ tailWord_5831758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831758).length < 2 ^ (prefixWord ++ tailWord_5831758).sum := by decide
  have hdescent : baseEnd_5831758 < baseStart_5831758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831791 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 8]
def baseStart_5831791 : Nat := 118140960795 + 5831791 * 2 ^ 59
def prefixEnd_5831791 : Nat := 4983230072969 + 3 ^ 40 * 5831791 * 2
def baseEnd_5831791 : Nat := 998170619854832608197529

theorem tailTrace_5831791 : CollatzResearch.WordTrace tailWord_5831791 prefixEnd_5831791 998170619854832608197529 := by
  unfold tailWord_5831791
  simp only [CollatzResearch.WordTrace]
  refine ⟨212702892015424672453047227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141801928010283114968698151 212702892015424672453047227)
  ·
    refine ⟨319054338023137008679570841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212702892015424672453047227 319054338023137008679570841)
    ·
      refine ⟨239290753517352756509678131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319054338023137008679570841 239290753517352756509678131)
      ·
        refine ⟨358936130276029134764517197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239290753517352756509678131 358936130276029134764517197)
        ·
          refine ⟨134601048853510925536693949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358936130276029134764517197 134601048853510925536693949)
          ·
            refine ⟨50475393320066597076260231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134601048853510925536693949 50475393320066597076260231)
            ·
              refine ⟨75713089980099895614390347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50475393320066597076260231 75713089980099895614390347)
              ·
                refine ⟨113569634970149843421585521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75713089980099895614390347 113569634970149843421585521)
                ·
                  refine ⟨85177226227612382566189141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113569634970149843421585521 85177226227612382566189141)
                  ·
                    refine ⟨998170619854832608197529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85177226227612382566189141 998170619854832608197529)
                    ·
                      rfl

theorem cell23_5831791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_5831791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831791 prefixEnd_5831791 := by exact prefixLift 5831791
  have htrace : WordTrace (prefixWord ++ tailWord_5831791) baseStart_5831791 baseEnd_5831791 := by
    simpa [prefixWord, tailWord_5831791, baseEnd_5831791] using wordTrace_append hprefix tailTrace_5831791
  have hstable : (prefixWord ++ tailWord_5831791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831791).length < 2 ^ (prefixWord ++ tailWord_5831791).sum := by decide
  have hdescent : baseEnd_5831791 < baseStart_5831791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831808 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_5831808 : Nat := 118140960795 + 5831808 * 2 ^ 59
def prefixEnd_5831808 : Nat := 4983230072969 + 3 ^ 40 * 5831808 * 2
def baseEnd_5831808 : Nat := 998173529578541419360003

theorem tailTrace_5831808 : CollatzResearch.WordTrace tailWord_5831808 prefixEnd_5831808 998173529578541419360003 := by
  unfold tailWord_5831808
  simp only [CollatzResearch.WordTrace]
  refine ⟨106351756028181542178208039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141802341370908722904277385 106351756028181542178208039)
  ·
    refine ⟨159527634042272313267312059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106351756028181542178208039 159527634042272313267312059)
    ·
      refine ⟨239291451063408469900968089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159527634042272313267312059 239291451063408469900968089)
      ·
        refine ⟨179468588297556352425726067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239291451063408469900968089 179468588297556352425726067)
        ·
          refine ⟨269202882446334528638589101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179468588297556352425726067 269202882446334528638589101)
          ·
            refine ⟨100951080917375448239470913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269202882446334528638589101 100951080917375448239470913)
            ·
              refine ⟨75713310688031586179603185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100951080917375448239470913 75713310688031586179603185)
              ·
                refine ⟨56784983016023689634702389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75713310688031586179603185 56784983016023689634702389)
                ·
                  refine ⟨5323592157752220903253349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56784983016023689634702389 5323592157752220903253349)
                  ·
                    refine ⟨998173529578541419360003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323592157752220903253349 998173529578541419360003)
                    ·
                      rfl

theorem cell23_5831808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_5831808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831808 prefixEnd_5831808 := by exact prefixLift 5831808
  have htrace : WordTrace (prefixWord ++ tailWord_5831808) baseStart_5831808 baseEnd_5831808 := by
    simpa [prefixWord, tailWord_5831808, baseEnd_5831808] using wordTrace_append hprefix tailTrace_5831808
  have hstable : (prefixWord ++ tailWord_5831808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831808).length < 2 ^ (prefixWord ++ tailWord_5831808).sum := by decide
  have hdescent : baseEnd_5831808 < baseStart_5831808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 4, 3, 2]
def baseStart_5831875 : Nat := 118140960795 + 5831875 * 2 ^ 59
def prefixEnd_5831875 : Nat := 4983230072969 + 3 ^ 40 * 5831875 * 2
def baseEnd_5831875 : Nat := 2994554991939475495942201

theorem tailTrace_5831875 : CollatzResearch.WordTrace tailWord_5831875 prefixEnd_5831875 2994554991939475495942201 := by
  unfold tailWord_5831875
  simp only [CollatzResearch.WordTrace]
  refine ⟨212705955747120354799105079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141803970498080236532736719 212705955747120354799105079)
  ·
    refine ⟨319058933620680532198657619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212705955747120354799105079 319058933620680532198657619)
    ·
      refine ⟨478588400431020798297986429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319058933620680532198657619 478588400431020798297986429)
      ·
        refine ⟨179470650161632799361744911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478588400431020798297986429 179470650161632799361744911)
        ·
          refine ⟨269205975242449199042617367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179470650161632799361744911 269205975242449199042617367)
          ·
            refine ⟨403808962863673798563926051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269205975242449199042617367 403808962863673798563926051)
            ·
              refine ⟨605713444295510697845889077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403808962863673798563926051 605713444295510697845889077)
              ·
                refine ⟨56785635402704127923052101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 605713444295510697845889077 56785635402704127923052101)
                ·
                  refine ⟨10647306638007023985572269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56785635402704127923052101 10647306638007023985572269)
                  ·
                    refine ⟨3992739989252633994589601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10647306638007023985572269 3992739989252633994589601)
                    ·
                      refine ⟨2994554991939475495942201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992739989252633994589601 2994554991939475495942201)
                      ·
                        rfl

theorem cell23_5831875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_5831875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831875 prefixEnd_5831875 := by exact prefixLift 5831875
  have htrace : WordTrace (prefixWord ++ tailWord_5831875) baseStart_5831875 baseEnd_5831875 := by
    simpa [prefixWord, tailWord_5831875, baseEnd_5831875] using wordTrace_append hprefix tailTrace_5831875
  have hstable : (prefixWord ++ tailWord_5831875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831875).length < 2 ^ (prefixWord ++ tailWord_5831875).sum := by decide
  have hdescent : baseEnd_5831875 < baseStart_5831875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831905 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5831905 : Nat := 118140960795 + 5831905 * 2 ^ 59
def prefixEnd_5831905 : Nat := 4983230072969 + 3 ^ 40 * 5831905 * 2
def baseEnd_5831905 : Nat := 2994570396359110378567063

theorem tailTrace_5831905 : CollatzResearch.WordTrace tailWord_5831905 prefixEnd_5831905 2994570396359110378567063 := by
  unfold tailWord_5831905
  simp only [CollatzResearch.WordTrace]
  refine ⟨212707049937011669922697169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141804699958007779948464779 212707049937011669922697169)
  ·
    refine ⟨159530287452758752442022877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212707049937011669922697169 159530287452758752442022877)
    ·
      refine ⟨59823857794784532165758579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159530287452758752442022877 59823857794784532165758579)
      ·
        refine ⟨89735786692176798248637869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59823857794784532165758579 89735786692176798248637869)
        ·
          refine ⟨33650920009566299343239201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89735786692176798248637869 33650920009566299343239201)
          ·
            refine ⟨25238190007174724507429401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33650920009566299343239201 25238190007174724507429401)
            ·
              refine ⟨18928642505381043380572051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25238190007174724507429401 18928642505381043380572051)
              ·
                refine ⟨28392963758071565070858077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18928642505381043380572051 28392963758071565070858077)
                ·
                  refine ⟨10647361409276836901571779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28392963758071565070858077 10647361409276836901571779)
                  ·
                    refine ⟨15971042113915255352357669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10647361409276836901571779 15971042113915255352357669)
                    ·
                      refine ⟨2994570396359110378567063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15971042113915255352357669 2994570396359110378567063)
                      ·
                        rfl

theorem cell23_5831905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5831905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831905 prefixEnd_5831905 := by exact prefixLift 5831905
  have htrace : WordTrace (prefixWord ++ tailWord_5831905) baseStart_5831905 baseEnd_5831905 := by
    simpa [prefixWord, tailWord_5831905, baseEnd_5831905] using wordTrace_append hprefix tailTrace_5831905
  have hstable : (prefixWord ++ tailWord_5831905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831905).length < 2 ^ (prefixWord ++ tailWord_5831905).sum := by decide
  have hdescent : baseEnd_5831905 < baseStart_5831905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831919 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 1, 5]
def baseStart_5831919 : Nat := 118140960795 + 5831919 * 2 ^ 59
def prefixEnd_5831919 : Nat := 4983230072969 + 3 ^ 40 * 5831919 * 2
def baseEnd_5831919 : Nat := 998192528362757774597333

theorem tailTrace_5831919 : CollatzResearch.WordTrace tailWord_5831919 prefixEnd_5831919 998192528362757774597333 := by
  unfold tailWord_5831919
  simp only [CollatzResearch.WordTrace]
  refine ⟨212707560558960950313706811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141805040372640633542471207 212707560558960950313706811)
  ·
    refine ⟨319061340838441425470560217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212707560558960950313706811 319061340838441425470560217)
    ·
      refine ⟨239296005628831069102920163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319061340838441425470560217 239296005628831069102920163)
      ·
        refine ⟨358944008443246603654380245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239296005628831069102920163 358944008443246603654380245)
        ·
          refine ⟨8412750197888592273149537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 358944008443246603654380245 8412750197888592273149537)
          ·
            refine ⟨6309562648416444204862153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8412750197888592273149537 6309562648416444204862153)
            ·
              refine ⟨4732171986312333153646615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309562648416444204862153 4732171986312333153646615)
              ·
                refine ⟨7098257979468499730469923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732171986312333153646615 7098257979468499730469923)
                ·
                  refine ⟨10647386969202749595704885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7098257979468499730469923 10647386969202749595704885)
                  ·
                    refine ⟨998192528362757774597333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10647386969202749595704885 998192528362757774597333)
                    ·
                      rfl

theorem cell23_5831919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_5831919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831919 prefixEnd_5831919 := by exact prefixLift 5831919
  have htrace : WordTrace (prefixWord ++ tailWord_5831919) baseStart_5831919 baseEnd_5831919 := by
    simpa [prefixWord, tailWord_5831919, baseEnd_5831919] using wordTrace_append hprefix tailTrace_5831919
  have hstable : (prefixWord ++ tailWord_5831919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831919).length < 2 ^ (prefixWord ++ tailWord_5831919).sum := by decide
  have hdescent : baseEnd_5831919 < baseStart_5831919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831932 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_5831932 : Nat := 118140960795 + 5831932 * 2 ^ 59
def prefixEnd_5831932 : Nat := 4983230072969 + 3 ^ 40 * 5831932 * 2
def baseEnd_5831932 : Nat := 998194753445593924309813

theorem tailTrace_5831932 : CollatzResearch.WordTrace tailWord_5831932 prefixEnd_5831932 998194753445593924309813 := by
  unfold tailWord_5831932
  simp only [CollatzResearch.WordTrace]
  refine ⟨106354017353956926766965025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141805356471942569022620033 106354017353956926766965025)
  ·
    refine ⟨79765513015467695075223769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106354017353956926766965025 79765513015467695075223769)
    ·
      refine ⟨59824134761600771306417827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79765513015467695075223769 59824134761600771306417827)
      ·
        refine ⟨89736202142401156959626741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59824134761600771306417827 89736202142401156959626741)
        ·
          refine ⟨8412768950850108464965007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89736202142401156959626741 8412768950850108464965007)
          ·
            refine ⟨12619153426275162697447511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412768950850108464965007 12619153426275162697447511)
            ·
              refine ⟨18928730139412744046171267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12619153426275162697447511 18928730139412744046171267)
              ·
                refine ⟨28393095209119116069256901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18928730139412744046171267 28393095209119116069256901)
                ·
                  refine ⟨5323705351709834262985669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28393095209119116069256901 5323705351709834262985669)
                  ·
                    refine ⟨998194753445593924309813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323705351709834262985669 998194753445593924309813)
                    ·
                      rfl

theorem cell23_5831932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_5831932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831932 prefixEnd_5831932 := by exact prefixLift 5831932
  have htrace : WordTrace (prefixWord ++ tailWord_5831932) baseStart_5831932 baseEnd_5831932 := by
    simpa [prefixWord, tailWord_5831932, baseEnd_5831932] using wordTrace_append hprefix tailTrace_5831932
  have hstable : (prefixWord ++ tailWord_5831932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831932).length < 2 ^ (prefixWord ++ tailWord_5831932).sum := by decide
  have hdescent : baseEnd_5831932 < baseStart_5831932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831939 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 3, 2, 2]
def baseStart_5831939 : Nat := 118140960795 + 5831939 * 2 ^ 59
def prefixEnd_5831939 : Nat := 4983230072969 + 3 ^ 40 * 5831939 * 2
def baseEnd_5831939 : Nat := 2994587854701363245541907

theorem tailTrace_5831939 : CollatzResearch.WordTrace tailWord_5831939 prefixEnd_5831939 2994587854701363245541907 := by
  unfold tailWord_5831939
  simp only [CollatzResearch.WordTrace]
  refine ⟨212708290018888493729434871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141805526679258995819623247 212708290018888493729434871)
  ·
    refine ⟨319062435028332740594152307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212708290018888493729434871 319062435028332740594152307)
    ·
      refine ⟨478593652542499110891228461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319062435028332740594152307 478593652542499110891228461)
      ·
        refine ⟨179472619703437166584210673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478593652542499110891228461 179472619703437166584210673)
        ·
          refine ⟨134604464777577874938158005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179472619703437166584210673 134604464777577874938158005)
          ·
            refine ⟨12619168572897925775452313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134604464777577874938158005 12619168572897925775452313)
            ·
              refine ⟨9464376429673444331589235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12619168572897925775452313 9464376429673444331589235)
              ·
                refine ⟨14196564644510166497383853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9464376429673444331589235 14196564644510166497383853)
                ·
                  refine ⟨5323711741691312436518945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14196564644510166497383853 5323711741691312436518945)
                  ·
                    refine ⟨3992783806268484327389209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5323711741691312436518945 3992783806268484327389209)
                    ·
                      refine ⟨2994587854701363245541907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992783806268484327389209 2994587854701363245541907)
                      ·
                        rfl

theorem cell23_5831939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_5831939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831939 prefixEnd_5831939 := by exact prefixLift 5831939
  have htrace : WordTrace (prefixWord ++ tailWord_5831939) baseStart_5831939 baseEnd_5831939 := by
    simpa [prefixWord, tailWord_5831939, baseEnd_5831939] using wordTrace_append hprefix tailTrace_5831939
  have hstable : (prefixWord ++ tailWord_5831939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831939).length < 2 ^ (prefixWord ++ tailWord_5831939).sum := by decide
  have hdescent : baseEnd_5831939 < baseStart_5831939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831962 : List Nat := [3, 1, 1, 3, 3, 3, 2, 7]
def baseStart_5831962 : Nat := 118140960795 + 5831962 * 2 ^ 59
def prefixEnd_5831962 : Nat := 4983230072969 + 3 ^ 40 * 5831962 * 2
def baseEnd_5831962 : Nat := 110911098694682098353863

theorem tailTrace_5831962 : CollatzResearch.WordTrace tailWord_5831962 prefixEnd_5831962 110911098694682098353863 := by
  unfold tailWord_5831962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53177282224451292164380535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141806085931870112438348093 53177282224451292164380535)
  ·
    refine ⟨79765923336676938246570803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53177282224451292164380535 79765923336676938246570803)
    ·
      refine ⟨119648885005015407369856205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79765923336676938246570803 119648885005015407369856205)
      ·
        refine ⟨44868331876880777763696077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119648885005015407369856205 44868331876880777763696077)
        ·
          refine ⟨16825624453830291661386029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44868331876880777763696077 16825624453830291661386029)
          ·
            refine ⟨6309609170186359373019761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16825624453830291661386029 6309609170186359373019761)
            ·
              refine ⟨4732206877639769529764821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309609170186359373019761 4732206877639769529764821)
              ·
                refine ⟨110911098694682098353863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4732206877639769529764821 110911098694682098353863)
                ·
                  rfl

theorem cell23_5831962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_5831962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831962 prefixEnd_5831962 := by exact prefixLift 5831962
  have htrace : WordTrace (prefixWord ++ tailWord_5831962) baseStart_5831962 baseEnd_5831962 := by
    simpa [prefixWord, tailWord_5831962, baseEnd_5831962] using wordTrace_append hprefix tailTrace_5831962
  have hstable : (prefixWord ++ tailWord_5831962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831962).length < 2 ^ (prefixWord ++ tailWord_5831962).sum := by decide
  have hdescent : baseEnd_5831962 < baseStart_5831962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831972 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_5831972 : Nat := 118140960795 + 5831972 * 2 ^ 59
def prefixEnd_5831972 : Nat := 4983230072969 + 3 ^ 40 * 5831972 * 2
def baseEnd_5831972 : Nat := 2994604799562961616429255

theorem tailTrace_5831972 : CollatzResearch.WordTrace tailWord_5831972 prefixEnd_5831972 2994604799562961616429255 := by
  unfold tailWord_5831972
  simp only [CollatzResearch.WordTrace]
  refine ⟨106354746813884470182693085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141806329085179293576924113 106354746813884470182693085)
  ·
    refine ⟨39883030055206676318509907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106354746813884470182693085 39883030055206676318509907)
    ·
      refine ⟨59824545082810014477764861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39883030055206676318509907 59824545082810014477764861)
      ·
        refine ⟨22434204406053755429161823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59824545082810014477764861 22434204406053755429161823)
        ·
          refine ⟨33651306609080633143742735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22434204406053755429161823 33651306609080633143742735)
          ·
            refine ⟨50476959913620949715614103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33651306609080633143742735 50476959913620949715614103)
            ·
              refine ⟨75715439870431424573421155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50476959913620949715614103 75715439870431424573421155)
              ·
                refine ⟨113573159805647136860131733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75715439870431424573421155 113573159805647136860131733)
                ·
                  refine ⟨5323741865889709540318675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113573159805647136860131733 5323741865889709540318675)
                  ·
                    refine ⟨7985612798834564310478013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5323741865889709540318675 7985612798834564310478013)
                    ·
                      refine ⟨2994604799562961616429255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7985612798834564310478013 2994604799562961616429255)
                      ·
                        rfl

theorem cell23_5831972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_5831972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831972 prefixEnd_5831972 := by exact prefixLift 5831972
  have htrace : WordTrace (prefixWord ++ tailWord_5831972) baseStart_5831972 baseEnd_5831972 := by
    simpa [prefixWord, tailWord_5831972, baseEnd_5831972] using wordTrace_append hprefix tailTrace_5831972
  have hstable : (prefixWord ++ tailWord_5831972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831972).length < 2 ^ (prefixWord ++ tailWord_5831972).sum := by decide
  have hdescent : baseEnd_5831972 < baseStart_5831972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831973 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 1, 2, 2]
def baseStart_5831973 : Nat := 118140960795 + 5831973 * 2 ^ 59
def prefixEnd_5831973 : Nat := 4983230072969 + 3 ^ 40 * 5831973 * 2
def baseEnd_5831973 : Nat := 2994605313043616112516751

theorem tailTrace_5831973 : CollatzResearch.WordTrace tailWord_5831973 prefixEnd_5831973 2994605313043616112516751 := by
  unfold tailWord_5831973
  simp only [CollatzResearch.WordTrace]
  refine ⟨212709530100765317536172573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141806353400510211690781715 212709530100765317536172573)
  ·
    refine ⟨79766073787786994076064715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212709530100765317536172573 79766073787786994076064715)
    ·
      refine ⟨119649110681680491114097073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79766073787786994076064715 119649110681680491114097073)
      ·
        refine ⟨89736833011260368335572805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119649110681680491114097073 89736833011260368335572805)
        ·
          refine ⟨16825656189611319062919901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89736833011260368335572805 16825656189611319062919901)
          ·
            refine ⟨6309621071104244648594963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16825656189611319062919901 6309621071104244648594963)
            ·
              refine ⟨9464431606656366972892445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309621071104244648594963 9464431606656366972892445)
              ·
                refine ⟨3549161852496137614834667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9464431606656366972892445 3549161852496137614834667)
                ·
                  refine ⟨5323742778744206422252001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549161852496137614834667 5323742778744206422252001)
                  ·
                    refine ⟨3992807084058154816689001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5323742778744206422252001 3992807084058154816689001)
                    ·
                      refine ⟨2994605313043616112516751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992807084058154816689001 2994605313043616112516751)
                      ·
                        rfl

theorem cell23_5831973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_5831973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831973 prefixEnd_5831973 := by exact prefixLift 5831973
  have htrace : WordTrace (prefixWord ++ tailWord_5831973) baseStart_5831973 baseEnd_5831973 := by
    simpa [prefixWord, tailWord_5831973, baseEnd_5831973] using wordTrace_append hprefix tailTrace_5831973
  have hstable : (prefixWord ++ tailWord_5831973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831973).length < 2 ^ (prefixWord ++ tailWord_5831973).sum := by decide
  have hdescent : baseEnd_5831973 < baseStart_5831973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5831990 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5831990 : Nat := 118140960795 + 5831990 * 2 ^ 59
def prefixEnd_5831990 : Nat := 4983230072969 + 3 ^ 40 * 5831990 * 2
def baseEnd_5831990 : Nat := 2994614042214742546004173

theorem tailTrace_5831990 : CollatzResearch.WordTrace tailWord_5831990 prefixEnd_5831990 2994614042214742546004173 := by
  unfold tailWord_5831990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294384383856483089971339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141806766761135819626360949 13294384383856483089971339)
  ·
    refine ⟨19941576575784724634957009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13294384383856483089971339 19941576575784724634957009)
    ·
      refine ⟨14956182431838543476217757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19941576575784724634957009 14956182431838543476217757)
      ·
        refine ⟨5608568411939453803581659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14956182431838543476217757 5608568411939453803581659)
        ·
          refine ⟨8412852617909180705372489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608568411939453803581659 8412852617909180705372489)
          ·
            refine ⟨6309639463431885529029367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8412852617909180705372489 6309639463431885529029367)
            ·
              refine ⟨9464459195147828293544051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309639463431885529029367 9464459195147828293544051)
              ·
                refine ⟨14196688792721742440316077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9464459195147828293544051 14196688792721742440316077)
                ·
                  refine ⟨5323758297270653415118529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14196688792721742440316077 5323758297270653415118529)
                  ·
                    refine ⟨3992818722952990061338897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5323758297270653415118529 3992818722952990061338897)
                    ·
                      refine ⟨2994614042214742546004173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3992818722952990061338897 2994614042214742546004173)
                      ·
                        rfl

theorem cell23_5831990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5831990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5831990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5831990 prefixEnd_5831990 := by exact prefixLift 5831990
  have htrace : WordTrace (prefixWord ++ tailWord_5831990) baseStart_5831990 baseEnd_5831990 := by
    simpa [prefixWord, tailWord_5831990, baseEnd_5831990] using wordTrace_append hprefix tailTrace_5831990
  have hstable : (prefixWord ++ tailWord_5831990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5831990).length < 2 ^ (prefixWord ++ tailWord_5831990).sum := by decide
  have hdescent : baseEnd_5831990 < baseStart_5831990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5831990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832163 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 1, 4]
def baseStart_5832163 : Nat := 118140960795 + 5832163 * 2 ^ 59
def prefixEnd_5832163 : Nat := 4983230072969 + 3 ^ 40 * 5832163 * 2
def baseEnd_5832163 : Nat := 998234291455990123046959

theorem tailTrace_5832163 : CollatzResearch.WordTrace tailWord_5832163 prefixEnd_5832163 998234291455990123046959 := by
  unfold tailWord_5832163
  simp only [CollatzResearch.WordTrace]
  refine ⟨212716459970076979985589143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141810973313384653323726095 212716459970076979985589143)
  ·
    refine ⟨319074689955115469978383715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212716459970076979985589143 319074689955115469978383715)
    ·
      refine ⟨478612034932673204967575573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319074689955115469978383715 478612034932673204967575573)
      ·
        refine ⟨22434939137469056482855105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 478612034932673204967575573 22434939137469056482855105)
        ·
          refine ⟨16826204353101792362141329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22434939137469056482855105 16826204353101792362141329)
          ·
            refine ⟨12619653264826344271605997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16826204353101792362141329 12619653264826344271605997)
            ·
              refine ⟨4732369974309879101852249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12619653264826344271605997 4732369974309879101852249)
              ·
                refine ⟨3549277480732409326389187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732369974309879101852249 3549277480732409326389187)
                ·
                  refine ⟨5323916221098613989583781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549277480732409326389187 5323916221098613989583781)
                  ·
                    refine ⟨998234291455990123046959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323916221098613989583781 998234291455990123046959)
                    ·
                      rfl

theorem cell23_5832163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 4].length) (baseStart_5832163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832163 prefixEnd_5832163 := by exact prefixLift 5832163
  have htrace : WordTrace (prefixWord ++ tailWord_5832163) baseStart_5832163 baseEnd_5832163 := by
    simpa [prefixWord, tailWord_5832163, baseEnd_5832163] using wordTrace_append hprefix tailTrace_5832163
  have hstable : (prefixWord ++ tailWord_5832163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832163).length < 2 ^ (prefixWord ++ tailWord_5832163).sum := by decide
  have hdescent : baseEnd_5832163 < baseStart_5832163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832189 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_5832189 : Nat := 118140960795 + 5832189 * 2 ^ 59
def prefixEnd_5832189 : Nat := 4983230072969 + 3 ^ 40 * 5832189 * 2
def baseEnd_5832189 : Nat := 998238741621662422471919

theorem tailTrace_5832189 : CollatzResearch.WordTrace tailWord_5832189 prefixEnd_5832189 998238741621662422471919 := by
  unfold tailWord_5832189
  simp only [CollatzResearch.WordTrace]
  refine ⟨212717408267982786426035621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141811605511988524284023747 212717408267982786426035621)
  ·
    refine ⟨39884514050246772454881679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212717408267982786426035621 39884514050246772454881679)
    ·
      refine ⟨59826771075370158682322519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39884514050246772454881679 59826771075370158682322519)
      ·
        refine ⟨89740156613055238023483779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59826771075370158682322519 89740156613055238023483779)
        ·
          refine ⟨134610234919582857035225669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89740156613055238023483779 134610234919582857035225669)
          ·
            refine ⟨25239419047421785694104813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134610234919582857035225669 25239419047421785694104813)
            ·
              refine ⟨9464782142783169635289305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25239419047421785694104813 9464782142783169635289305)
              ·
                refine ⟨7098586607087377226466979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9464782142783169635289305 7098586607087377226466979)
                ·
                  refine ⟨10647879910631065839700469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7098586607087377226466979 10647879910631065839700469)
                  ·
                    refine ⟨998238741621662422471919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10647879910631065839700469 998238741621662422471919)
                    ·
                      rfl

theorem cell23_5832189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_5832189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832189 prefixEnd_5832189 := by exact prefixLift 5832189
  have htrace : WordTrace (prefixWord ++ tailWord_5832189) baseStart_5832189 baseEnd_5832189 := by
    simpa [prefixWord, tailWord_5832189, baseEnd_5832189] using wordTrace_append hprefix tailTrace_5832189
  have hstable : (prefixWord ++ tailWord_5832189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832189).length < 2 ^ (prefixWord ++ tailWord_5832189).sum := by decide
  have hdescent : baseEnd_5832189 < baseStart_5832189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832202 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_5832202 : Nat := 118140960795 + 5832202 * 2 ^ 59
def prefixEnd_5832202 : Nat := 4983230072969 + 3 ^ 40 * 5832202 * 2
def baseEnd_5832202 : Nat := 998240966704498572184399

theorem tailTrace_5832202 : CollatzResearch.WordTrace tailWord_5832202 prefixEnd_5832202 998240966704498572184399 := by
  unfold tailWord_5832202
  simp only [CollatzResearch.WordTrace]
  refine ⟨53179470604233922411564715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141811921611290459764172573 53179470604233922411564715)
  ·
    refine ⟨79769205906350883617347073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53179470604233922411564715 79769205906350883617347073)
    ·
      refine ⟨59826904429763162713010305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79769205906350883617347073 59826904429763162713010305)
      ·
        refine ⟨44870178322322372034757729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59826904429763162713010305 44870178322322372034757729)
        ·
          refine ⟨33652633741741779026068297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44870178322322372034757729 33652633741741779026068297)
          ·
            refine ⟨25239475306306334269551223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33652633741741779026068297 25239475306306334269551223)
            ·
              refine ⟨37859212959459501404326835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25239475306306334269551223 37859212959459501404326835)
              ·
                refine ⟨56788819439189252106490253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37859212959459501404326835 56788819439189252106490253)
                ·
                  refine ⟨21295807289695969539933845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56788819439189252106490253 21295807289695969539933845)
                  ·
                    refine ⟨998240966704498572184399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21295807289695969539933845 998240966704498572184399)
                    ·
                      rfl

theorem cell23_5832202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_5832202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832202 prefixEnd_5832202 := by exact prefixLift 5832202
  have htrace : WordTrace (prefixWord ++ tailWord_5832202) baseStart_5832202 baseEnd_5832202 := by
    simpa [prefixWord, tailWord_5832202, baseEnd_5832202] using wordTrace_append hprefix tailTrace_5832202
  have hstable : (prefixWord ++ tailWord_5832202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832202).length < 2 ^ (prefixWord ++ tailWord_5832202).sum := by decide
  have hdescent : baseEnd_5832202 < baseStart_5832202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832215 : List Nat := [1, 1, 3, 18]
def baseStart_5832215 : Nat := 118140960795 + 5832215 * 2 ^ 59
def prefixEnd_5832215 : Nat := 4983230072969 + 3 ^ 40 * 5832215 * 2
def baseEnd_5832215 : Nat := 1369332224673984529351

theorem tailTrace_5832215 : CollatzResearch.WordTrace tailWord_5832215 prefixEnd_5832215 1369332224673984529351 := by
  unfold tailWord_5832215
  simp only [CollatzResearch.WordTrace]
  refine ⟨212718356565888592866482099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141812237710592395244321399 212718356565888592866482099)
  ·
    refine ⟨319077534848832889299723149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212718356565888592866482099 319077534848832889299723149)
    ·
      refine ⟨119654075568312333487396181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319077534848832889299723149 119654075568312333487396181)
      ·
        refine ⟨1369332224673984529351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 119654075568312333487396181 1369332224673984529351)
        ·
          rfl

theorem cell23_5832215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 18].length) (baseStart_5832215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832215 prefixEnd_5832215 := by exact prefixLift 5832215
  have htrace : WordTrace (prefixWord ++ tailWord_5832215) baseStart_5832215 baseEnd_5832215 := by
    simpa [prefixWord, tailWord_5832215, baseEnd_5832215] using wordTrace_append hprefix tailTrace_5832215
  have hstable : (prefixWord ++ tailWord_5832215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832215).length < 2 ^ (prefixWord ++ tailWord_5832215).sum := by decide
  have hdescent : baseEnd_5832215 < baseStart_5832215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832249 : List Nat := [1, 2, 1, 5, 1, 3, 3, 7]
def baseStart_5832249 : Nat := 118140960795 + 5832249 * 2 ^ 59
def prefixEnd_5832249 : Nat := 4983230072969 + 3 ^ 40 * 5832249 * 2
def baseEnd_5832249 : Nat := 110916556803861371580203

theorem tailTrace_5832249 : CollatzResearch.WordTrace tailWord_5832249 prefixEnd_5832249 110916556803861371580203 := by
  unfold tailWord_5832249
  simp only [CollatzResearch.WordTrace]
  refine ⟨212719596647765416673219801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141813064431843611115479867 212719596647765416673219801)
  ·
    refine ⟨159539697485824062504914851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212719596647765416673219801 159539697485824062504914851)
    ·
      refine ⟨239309546228736093757372277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159539697485824062504914851 239309546228736093757372277)
      ·
        refine ⟨22435269958944008789753651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239309546228736093757372277 22435269958944008789753651)
        ·
          refine ⟨33652904938416013184630477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22435269958944008789753651 33652904938416013184630477)
          ·
            refine ⟨12619839351906004944236429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33652904938416013184630477 12619839351906004944236429)
            ·
              refine ⟨4732439756964751854088661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12619839351906004944236429 4732439756964751854088661)
              ·
                refine ⟨110916556803861371580203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4732439756964751854088661 110916556803861371580203)
                ·
                  rfl

theorem cell23_5832249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 7].length) (baseStart_5832249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832249 prefixEnd_5832249 := by exact prefixLift 5832249
  have htrace : WordTrace (prefixWord ++ tailWord_5832249) baseStart_5832249 baseEnd_5832249 := by
    simpa [prefixWord, tailWord_5832249, baseEnd_5832249] using wordTrace_append hprefix tailTrace_5832249
  have hstable : (prefixWord ++ tailWord_5832249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832249).length < 2 ^ (prefixWord ++ tailWord_5832249).sum := by decide
  have hdescent : baseEnd_5832249 < baseStart_5832249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832276 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_5832276 : Nat := 118140960795 + 5832276 * 2 ^ 59
def prefixEnd_5832276 : Nat := 4983230072969 + 3 ^ 40 * 5832276 * 2
def baseEnd_5832276 : Nat := 2994760897681928427027857

theorem tailTrace_5832276 : CollatzResearch.WordTrace tailWord_5832276 prefixEnd_5832276 2994760897681928427027857 := by
  unfold tailWord_5832276
  simp only [CollatzResearch.WordTrace]
  refine ⟨106360290709333800142226341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141813720945778400189635121 106360290709333800142226341)
  ·
    refine ⟨19942554508000087526667439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106360290709333800142226341 19942554508000087526667439)
    ·
      refine ⟨29913831762000131290001159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19942554508000087526667439 29913831762000131290001159)
      ·
        refine ⟨44870747643000196935001739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29913831762000131290001159 44870747643000196935001739)
        ·
          refine ⟨67306121464500295402502609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44870747643000196935001739 67306121464500295402502609)
          ·
            refine ⟨50479591098375221551876957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67306121464500295402502609 50479591098375221551876957)
            ·
              refine ⟨18929846661890708081953859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50479591098375221551876957 18929846661890708081953859)
              ·
                refine ⟨28394769992836062122930789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18929846661890708081953859 28394769992836062122930789)
                ·
                  refine ⟨5324019373656761648049523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28394769992836062122930789 5324019373656761648049523)
                  ·
                    refine ⟨7986029060485142472074285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5324019373656761648049523 7986029060485142472074285)
                    ·
                      refine ⟨2994760897681928427027857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986029060485142472074285 2994760897681928427027857)
                      ·
                        rfl

theorem cell23_5832276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_5832276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832276 prefixEnd_5832276 := by exact prefixLift 5832276
  have htrace : WordTrace (prefixWord ++ tailWord_5832276) baseStart_5832276 baseEnd_5832276 := by
    simpa [prefixWord, tailWord_5832276, baseEnd_5832276] using wordTrace_append hprefix tailTrace_5832276
  have hstable : (prefixWord ++ tailWord_5832276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832276).length < 2 ^ (prefixWord ++ tailWord_5832276).sum := by decide
  have hdescent : baseEnd_5832276 < baseStart_5832276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832282 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_5832282 : Nat := 118140960795 + 5832282 * 2 ^ 59
def prefixEnd_5832282 : Nat := 4983230072969 + 3 ^ 40 * 5832282 * 2
def baseEnd_5832282 : Nat := 2994763978565855403552829

theorem tailTrace_5832282 : CollatzResearch.WordTrace tailWord_5832282 prefixEnd_5832282 2994763978565855403552829 := by
  unfold tailWord_5832282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53180200064161465827292775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141813866837763908872780733 53180200064161465827292775)
  ·
    refine ⟨79770300096242198740939163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53180200064161465827292775 79770300096242198740939163)
    ·
      refine ⟨119655450144363298111408745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79770300096242198740939163 119655450144363298111408745)
      ·
        refine ⟨89741587608272473583556559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119655450144363298111408745 89741587608272473583556559)
        ·
          refine ⟨134612381412408710375334839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89741587608272473583556559 134612381412408710375334839)
          ·
            refine ⟨201918572118613065563002259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134612381412408710375334839 201918572118613065563002259)
            ·
              refine ⟨302877858177919598344503389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201918572118613065563002259 302877858177919598344503389)
              ·
                refine ⟨113579196816719849379188771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302877858177919598344503389 113579196816719849379188771)
                ·
                  refine ⟨170368795225079774068783157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113579196816719849379188771 170368795225079774068783157)
                  ·
                    refine ⟨15972074552351228818948421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 170368795225079774068783157 15972074552351228818948421)
                    ·
                      refine ⟨2994763978565855403552829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15972074552351228818948421 2994763978565855403552829)
                      ·
                        rfl

theorem cell23_5832282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_5832282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832282 prefixEnd_5832282 := by exact prefixLift 5832282
  have htrace : WordTrace (prefixWord ++ tailWord_5832282) baseStart_5832282 baseEnd_5832282 := by
    simpa [prefixWord, tailWord_5832282, baseEnd_5832282] using wordTrace_append hprefix tailTrace_5832282
  have hstable : (prefixWord ++ tailWord_5832282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832282).length < 2 ^ (prefixWord ++ tailWord_5832282).sum := by decide
  have hdescent : baseEnd_5832282 < baseStart_5832282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832332 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5832332 : Nat := 118140960795 + 5832332 * 2 ^ 59
def prefixEnd_5832332 : Nat := 4983230072969 + 3 ^ 40 * 5832332 * 2
def baseEnd_5832332 : Nat := 2994789652598580207927599

theorem tailTrace_5832332 : CollatzResearch.WordTrace tailWord_5832332 prefixEnd_5832332 2994789652598580207927599 := by
  unfold tailWord_5832332
  simp only [CollatzResearch.WordTrace]
  refine ⟨106361311953232360924245625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141815082604309814565660833 106361311953232360924245625)
  ·
    refine ⟨79770983964924270693184219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106361311953232360924245625 79770983964924270693184219)
    ·
      refine ⟨119656475947386406039776329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79770983964924270693184219 119656475947386406039776329)
      ·
        refine ⟨89742356960539804529832247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119656475947386406039776329 89742356960539804529832247)
        ·
          refine ⟨134613535440809706794748371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89742356960539804529832247 134613535440809706794748371)
          ·
            refine ⟨201920303161214560192122557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134613535440809706794748371 201920303161214560192122557)
            ·
              refine ⟨75720113685455460072045959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201920303161214560192122557 75720113685455460072045959)
              ·
                refine ⟨113580170528183190108068939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75720113685455460072045959 113580170528183190108068939)
                ·
                  refine ⟨170370255792274785162103409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113580170528183190108068939 170370255792274785162103409)
                  ·
                    refine ⟨127777691844206088871577557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170370255792274785162103409 127777691844206088871577557)
                    ·
                      refine ⟨2994789652598580207927599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127777691844206088871577557 2994789652598580207927599)
                      ·
                        rfl

theorem cell23_5832332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5832332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832332 prefixEnd_5832332 := by exact prefixLift 5832332
  have htrace : WordTrace (prefixWord ++ tailWord_5832332) baseStart_5832332 baseEnd_5832332 := by
    simpa [prefixWord, tailWord_5832332, baseEnd_5832332] using wordTrace_append hprefix tailTrace_5832332
  have hstable : (prefixWord ++ tailWord_5832332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832332).length < 2 ^ (prefixWord ++ tailWord_5832332).sum := by decide
  have hdescent : baseEnd_5832332 < baseStart_5832332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832349 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_5832349 : Nat := 118140960795 + 5832349 * 2 ^ 59
def prefixEnd_5832349 : Nat := 4983230072969 + 3 ^ 40 * 5832349 * 2
def baseEnd_5832349 : Nat := 2994798381769706641415021

theorem tailTrace_5832349 : CollatzResearch.WordTrace tailWord_5832349 prefixEnd_5832349 2994798381769706641415021 := by
  unfold tailWord_5832349
  simp only [CollatzResearch.WordTrace]
  refine ⟨212723243947403133751860101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141815495964935422501240067 212723243947403133751860101)
  ·
    refine ⟨39885608240138087578473769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212723243947403133751860101 39885608240138087578473769)
    ·
      refine ⟨29914206180103565683855327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39885608240138087578473769 29914206180103565683855327)
      ·
        refine ⟨44871309270155348525782991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29914206180103565683855327 44871309270155348525782991)
        ·
          refine ⟨67306963905233022788674487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44871309270155348525782991 67306963905233022788674487)
          ·
            refine ⟨100960445857849534183011731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67306963905233022788674487 100960445857849534183011731)
            ·
              refine ⟨151440668786774301274517597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100960445857849534183011731 151440668786774301274517597)
              ·
                refine ⟨56790250795040362977944099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151440668786774301274517597 56790250795040362977944099)
                ·
                  refine ⟨85185376192560544466916149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56790250795040362977944099 85185376192560544466916149)
                  ·
                    refine ⟨7986129018052551043773389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85185376192560544466916149 7986129018052551043773389)
                    ·
                      refine ⟨2994798381769706641415021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986129018052551043773389 2994798381769706641415021)
                      ·
                        rfl

theorem cell23_5832349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_5832349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832349 prefixEnd_5832349 := by exact prefixLift 5832349
  have htrace : WordTrace (prefixWord ++ tailWord_5832349) baseStart_5832349 baseEnd_5832349 := by
    simpa [prefixWord, tailWord_5832349, baseEnd_5832349] using wordTrace_append hprefix tailTrace_5832349
  have hstable : (prefixWord ++ tailWord_5832349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832349).length < 2 ^ (prefixWord ++ tailWord_5832349).sum := by decide
  have hdescent : baseEnd_5832349 < baseStart_5832349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832354 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5832354 : Nat := 118140960795 + 5832354 * 2 ^ 59
def prefixEnd_5832354 : Nat := 4983230072969 + 3 ^ 40 * 5832354 * 2
def baseEnd_5832354 : Nat := 2994800949172979121852499

theorem tailTrace_5832354 : CollatzResearch.WordTrace tailWord_5832354 prefixEnd_5832354 2994800949172979121852499 := by
  unfold tailWord_5832354
  simp only [CollatzResearch.WordTrace]
  refine ⟨53180856578096254901448029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141815617541590013070528077 53180856578096254901448029)
  ·
    refine ⟨19942821216786095588043011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53180856578096254901448029 19942821216786095588043011)
    ·
      refine ⟨29914231825179143382064517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19942821216786095588043011 29914231825179143382064517)
      ·
        refine ⟨5608918467221089384137097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29914231825179143382064517 5608918467221089384137097)
        ·
          refine ⟨4206688850415817038102823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5608918467221089384137097 4206688850415817038102823)
          ·
            refine ⟨6310033275623725557154235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206688850415817038102823 6310033275623725557154235)
            ·
              refine ⟨9465049913435588335731353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310033275623725557154235 9465049913435588335731353)
              ·
                refine ⟨7098787435076691251798515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9465049913435588335731353 7098787435076691251798515)
                ·
                  refine ⟨10648181152615036877697773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7098787435076691251798515 10648181152615036877697773)
                  ·
                    refine ⟨3993067932230638829136665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10648181152615036877697773 3993067932230638829136665)
                    ·
                      refine ⟨2994800949172979121852499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993067932230638829136665 2994800949172979121852499)
                      ·
                        rfl

theorem cell23_5832354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5832354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832354 prefixEnd_5832354 := by exact prefixLift 5832354
  have htrace : WordTrace (prefixWord ++ tailWord_5832354) baseStart_5832354 baseEnd_5832354 := by
    simpa [prefixWord, tailWord_5832354, baseEnd_5832354] using wordTrace_append hprefix tailTrace_5832354
  have hstable : (prefixWord ++ tailWord_5832354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832354).length < 2 ^ (prefixWord ++ tailWord_5832354).sum := by decide
  have hdescent : baseEnd_5832354 < baseStart_5832354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832399 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 7, 4]
def baseStart_5832399 : Nat := 118140960795 + 5832399 * 2 ^ 59
def prefixEnd_5832399 : Nat := 4983230072969 + 3 ^ 40 * 5832399 * 2
def baseEnd_5832399 : Nat := 998274685267477148596597

theorem tailTrace_5832399 : CollatzResearch.WordTrace tailWord_5832399 prefixEnd_5832399 998274685267477148596597 := by
  unfold tailWord_5832399
  simp only [CollatzResearch.WordTrace]
  refine ⟨212725067597221992291180251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141816711731481328194120167 212725067597221992291180251)
  ·
    refine ⟨319087601395832988436770377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212725067597221992291180251 319087601395832988436770377)
    ·
      refine ⟨239315701046874741327577783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319087601395832988436770377 239315701046874741327577783)
      ·
        refine ⟨358973551570312111991366675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239315701046874741327577783 358973551570312111991366675)
        ·
          refine ⟨538460327355468167987050013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358973551570312111991366675 538460327355468167987050013)
          ·
            refine ⟨201922622758300562995143755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538460327355468167987050013 201922622758300562995143755)
            ·
              refine ⟨302883934137450844492715633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201922622758300562995143755 302883934137450844492715633)
              ·
                refine ⟨227162950603088133369536725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302883934137450844492715633 227162950603088133369536725)
                ·
                  refine ⟨5324131654759878125848517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 227162950603088133369536725 5324131654759878125848517)
                  ·
                    refine ⟨998274685267477148596597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324131654759878125848517 998274685267477148596597)
                    ·
                      rfl

theorem cell23_5832399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_5832399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832399 prefixEnd_5832399 := by exact prefixLift 5832399
  have htrace : WordTrace (prefixWord ++ tailWord_5832399) baseStart_5832399 baseEnd_5832399 := by
    simpa [prefixWord, tailWord_5832399, baseEnd_5832399] using wordTrace_append hprefix tailTrace_5832399
  have hstable : (prefixWord ++ tailWord_5832399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832399).length < 2 ^ (prefixWord ++ tailWord_5832399).sum := by decide
  have hdescent : baseEnd_5832399 < baseStart_5832399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832423 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5832423 : Nat := 118140960795 + 5832423 * 2 ^ 59
def prefixEnd_5832423 : Nat := 4983230072969 + 3 ^ 40 * 5832423 * 2
def baseEnd_5832423 : Nat := 2994836379338139351889681

theorem tailTrace_5832423 : CollatzResearch.WordTrace tailWord_5832423 prefixEnd_5832423 2994836379338139351889681 := by
  unfold tailWord_5832423
  simp only [CollatzResearch.WordTrace]
  refine ⟨212725942949135044390053923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141817295299423362926702615 212725942949135044390053923)
  ·
    refine ⟨319088914423702566585080885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212725942949135044390053923 319088914423702566585080885)
    ·
      refine ⟨29914585727222115617351333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319088914423702566585080885 29914585727222115617351333)
      ·
        refine ⟨5608984823854146678253375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29914585727222115617351333 5608984823854146678253375)
        ·
          refine ⟨8413477235781220017380063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608984823854146678253375 8413477235781220017380063)
          ·
            refine ⟨12620215853671830026070095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8413477235781220017380063 12620215853671830026070095)
            ·
              refine ⟨18930323780507745039105143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12620215853671830026070095 18930323780507745039105143)
              ·
                refine ⟨28395485670761617558657715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18930323780507745039105143 28395485670761617558657715)
                ·
                  refine ⟨42593228506142426337986573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28395485670761617558657715 42593228506142426337986573)
                  ·
                    refine ⟨15972460689803409876744965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42593228506142426337986573 15972460689803409876744965)
                    ·
                      refine ⟨2994836379338139351889681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15972460689803409876744965 2994836379338139351889681)
                      ·
                        rfl

theorem cell23_5832423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5832423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832423 prefixEnd_5832423 := by exact prefixLift 5832423
  have htrace : WordTrace (prefixWord ++ tailWord_5832423) baseStart_5832423 baseEnd_5832423 := by
    simpa [prefixWord, tailWord_5832423, baseEnd_5832423] using wordTrace_append hprefix tailTrace_5832423
  have hstable : (prefixWord ++ tailWord_5832423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832423).length < 2 ^ (prefixWord ++ tailWord_5832423).sum := by decide
  have hdescent : baseEnd_5832423 < baseStart_5832423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832433 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 1, 4]
def baseStart_5832433 : Nat := 118140960795 + 5832433 * 2 ^ 59
def prefixEnd_5832433 : Nat := 4983230072969 + 3 ^ 40 * 5832433 * 2
def baseEnd_5832433 : Nat := 998280504714894770921545

theorem tailTrace_5832433 : CollatzResearch.WordTrace tailWord_5832433 prefixEnd_5832433 998280504714894770921545 := by
  unfold tailWord_5832433
  simp only [CollatzResearch.WordTrace]
  refine ⟨212726307679098816097917953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141817538452732544065278635 212726307679098816097917953)
  ·
    refine ⟨159544730759324112073438465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212726307679098816097917953 159544730759324112073438465)
    ·
      refine ⟨119658548069493084055078849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159544730759324112073438465 119658548069493084055078849)
      ·
        refine ⟨89743911052119813041309137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119658548069493084055078849 89743911052119813041309137)
        ·
          refine ⟨67307933289089859780981853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89743911052119813041309137 67307933289089859780981853)
          ·
            refine ⟨25240474983408697417868195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67307933289089859780981853 25240474983408697417868195)
            ·
              refine ⟨37860712475113046126802293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25240474983408697417868195 37860712475113046126802293)
              ·
                refine ⟨3549441794541848074387715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37860712475113046126802293 3549441794541848074387715)
                ·
                  refine ⟨5324162691812772111581573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549441794541848074387715 5324162691812772111581573)
                  ·
                    refine ⟨998280504714894770921545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324162691812772111581573 998280504714894770921545)
                    ·
                      rfl

theorem cell23_5832433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_5832433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832433 prefixEnd_5832433 := by exact prefixLift 5832433
  have htrace : WordTrace (prefixWord ++ tailWord_5832433) baseStart_5832433 baseEnd_5832433 := by
    simpa [prefixWord, tailWord_5832433, baseEnd_5832433] using wordTrace_append hprefix tailTrace_5832433
  have hstable : (prefixWord ++ tailWord_5832433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832433).length < 2 ^ (prefixWord ++ tailWord_5832433).sum := by decide
  have hdescent : baseEnd_5832433 < baseStart_5832433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832449 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_5832449 : Nat := 118140960795 + 5832449 * 2 ^ 59
def prefixEnd_5832449 : Nat := 4983230072969 + 3 ^ 40 * 5832449 * 2
def baseEnd_5832449 : Nat := 2994849729835156250164561

theorem tailTrace_5832449 : CollatzResearch.WordTrace tailWord_5832449 prefixEnd_5832449 2994849729835156250164561 := by
  unfold tailWord_5832449
  simp only [CollatzResearch.WordTrace]
  refine ⟨212726891247040850830500401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141817927498027233887000267 212726891247040850830500401)
  ·
    refine ⟨159545168435280638122875301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212726891247040850830500401 159545168435280638122875301)
    ·
      refine ⟨29914719081615119648039119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159545168435280638122875301 29914719081615119648039119)
      ·
        refine ⟨44872078622422679472058679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29914719081615119648039119 44872078622422679472058679)
        ·
          refine ⟨67308117933634019208088019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44872078622422679472058679 67308117933634019208088019)
          ·
            refine ⟨100962176900451028812132029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67308117933634019208088019 100962176900451028812132029)
            ·
              refine ⟨37860816337669135804549511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100962176900451028812132029 37860816337669135804549511)
              ·
                refine ⟨56791224506503703706824267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37860816337669135804549511 56791224506503703706824267)
                ·
                  refine ⟨85186836759755555560236401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56791224506503703706824267 85186836759755555560236401)
                  ·
                    refine ⟨63890127569816666670177301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85186836759755555560236401 63890127569816666670177301)
                    ·
                      refine ⟨2994849729835156250164561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63890127569816666670177301 2994849729835156250164561)
                      ·
                        rfl

theorem cell23_5832449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_5832449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832449 prefixEnd_5832449 := by exact prefixLift 5832449
  have htrace : WordTrace (prefixWord ++ tailWord_5832449) baseStart_5832449 baseEnd_5832449 := by
    simpa [prefixWord, tailWord_5832449, baseEnd_5832449] using wordTrace_append hprefix tailTrace_5832449
  have hstable : (prefixWord ++ tailWord_5832449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832449).length < 2 ^ (prefixWord ++ tailWord_5832449).sum := by decide
  have hdescent : baseEnd_5832449 < baseStart_5832449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832450 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_5832450 : Nat := 118140960795 + 5832450 * 2 ^ 59
def prefixEnd_5832450 : Nat := 4983230072969 + 3 ^ 40 * 5832450 * 2
def baseEnd_5832450 : Nat := 998283414438603582084019

theorem tailTrace_5832450 : CollatzResearch.WordTrace tailWord_5832450 prefixEnd_5832450 998283414438603582084019 := by
  unfold tailWord_5832450
  simp only [CollatzResearch.WordTrace]
  refine ⟨53181731930009307000321701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141817951813358152000857869 53181731930009307000321701)
  ·
    refine ⟨9971574736876745062560319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53181731930009307000321701 9971574736876745062560319)
    ·
      refine ⟨14957362105315117593840479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9971574736876745062560319 14957362105315117593840479)
      ·
        refine ⟨22436043157972676390760719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957362105315117593840479 22436043157972676390760719)
        ·
          refine ⟨33654064736959014586141079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22436043157972676390760719 33654064736959014586141079)
          ·
            refine ⟨50481097105438521879211619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33654064736959014586141079 50481097105438521879211619)
            ·
              refine ⟨75721645658157782818817429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50481097105438521879211619 75721645658157782818817429)
              ·
                refine ⟨3549452140226146069632067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75721645658157782818817429 3549452140226146069632067)
                ·
                  refine ⟨5324178210339219104448101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549452140226146069632067 5324178210339219104448101)
                  ·
                    refine ⟨998283414438603582084019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324178210339219104448101 998283414438603582084019)
                    ·
                      rfl

theorem cell23_5832450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_5832450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832450 prefixEnd_5832450 := by exact prefixLift 5832450
  have htrace : WordTrace (prefixWord ++ tailWord_5832450) baseStart_5832450 baseEnd_5832450 := by
    simpa [prefixWord, tailWord_5832450, baseEnd_5832450] using wordTrace_append hprefix tailTrace_5832450
  have hstable : (prefixWord ++ tailWord_5832450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832450).length < 2 ^ (prefixWord ++ tailWord_5832450).sum := by decide
  have hdescent : baseEnd_5832450 < baseStart_5832450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832459 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 5, 5]
def baseStart_5832459 : Nat := 118140960795 + 5832459 * 2 ^ 59
def prefixEnd_5832459 : Nat := 4983230072969 + 3 ^ 40 * 5832459 * 2
def baseEnd_5832459 : Nat := 998284954880567070346505

theorem tailTrace_5832459 : CollatzResearch.WordTrace tailWord_5832459 prefixEnd_5832459 998284954880567070346505 := by
  unfold tailWord_5832459
  simp only [CollatzResearch.WordTrace]
  refine ⟨212727255977004622538364431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141818170651336415025576287 212727255977004622538364431)
  ·
    refine ⟨319090883965506933807546647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212727255977004622538364431 319090883965506933807546647)
    ·
      refine ⟨478636325948260400711319971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319090883965506933807546647 478636325948260400711319971)
      ·
        refine ⟨717954488922390601066979957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478636325948260400711319971 717954488922390601066979957)
        ·
          refine ⟨67308233336474118850029371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 717954488922390601066979957 67308233336474118850029371)
          ·
            refine ⟨100962350004711178275044057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67308233336474118850029371 100962350004711178275044057)
            ·
              refine ⟨75721762503533383706283043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100962350004711178275044057 75721762503533383706283043)
              ·
                refine ⟨113582643755300075559424565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75721762503533383706283043 113582643755300075559424565)
                ·
                  refine ⟨10648372852059382083696053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113582643755300075559424565 10648372852059382083696053)
                  ·
                    refine ⟨998284954880567070346505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10648372852059382083696053 998284954880567070346505)
                    ·
                      rfl

theorem cell23_5832459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 5].length) (baseStart_5832459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832459 prefixEnd_5832459 := by exact prefixLift 5832459
  have htrace : WordTrace (prefixWord ++ tailWord_5832459) baseStart_5832459 baseEnd_5832459 := by
    simpa [prefixWord, tailWord_5832459, baseEnd_5832459] using wordTrace_append hprefix tailTrace_5832459
  have hstable : (prefixWord ++ tailWord_5832459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832459).length < 2 ^ (prefixWord ++ tailWord_5832459).sum := by decide
  have hdescent : baseEnd_5832459 < baseStart_5832459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832500 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_5832500 : Nat := 118140960795 + 5832500 * 2 ^ 59
def prefixEnd_5832500 : Nat := 4983230072969 + 3 ^ 40 * 5832500 * 2
def baseEnd_5832500 : Nat := 2994875917348535550626827

theorem tailTrace_5832500 : CollatzResearch.WordTrace tailWord_5832500 prefixEnd_5832500 2994875917348535550626827 := by
  unfold tailWord_5832500
  simp only [CollatzResearch.WordTrace]
  refine ⟨106364375684928043270303477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141819167579904057693737969 106364375684928043270303477)
  ·
    refine ⟨9971660220462004056590951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106364375684928043270303477 9971660220462004056590951)
    ·
      refine ⟨14957490330693006084886427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9971660220462004056590951 14957490330693006084886427)
      ·
        refine ⟨22436235496039509127329641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957490330693006084886427 22436235496039509127329641)
        ·
          refine ⟨16827176622029631845497231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22436235496039509127329641 16827176622029631845497231)
          ·
            refine ⟨25240764933044447768245847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16827176622029631845497231 25240764933044447768245847)
            ·
              refine ⟨37861147399566671652368771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25240764933044447768245847 37861147399566671652368771)
              ·
                refine ⟨56791721099350007478553157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37861147399566671652368771 56791721099350007478553157)
                ·
                  refine ⟨10648447706128126402228717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56791721099350007478553157 10648447706128126402228717)
                  ·
                    refine ⟨3993167889798047400835769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10648447706128126402228717 3993167889798047400835769)
                    ·
                      refine ⟨2994875917348535550626827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993167889798047400835769 2994875917348535550626827)
                      ·
                        rfl

theorem cell23_5832500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_5832500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832500 prefixEnd_5832500 := by exact prefixLift 5832500
  have htrace : WordTrace (prefixWord ++ tailWord_5832500) baseStart_5832500 baseEnd_5832500 := by
    simpa [prefixWord, tailWord_5832500, baseEnd_5832500] using wordTrace_append hprefix tailTrace_5832500
  have hstable : (prefixWord ++ tailWord_5832500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832500).length < 2 ^ (prefixWord ++ tailWord_5832500).sum := by decide
  have hdescent : baseEnd_5832500 < baseStart_5832500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832519 : List Nat := [1, 1, 4, 1, 2, 1, 3, 10]
def baseStart_5832519 : Nat := 118140960795 + 5832519 * 2 ^ 59
def prefixEnd_5832519 : Nat := 4983230072969 + 3 ^ 40 * 5832519 * 2
def baseEnd_5832519 : Nat := 110921691610406332455157

theorem tailTrace_5832519 : CollatzResearch.WordTrace tailWord_5832519 prefixEnd_5832519 110921691610406332455157 := by
  unfold tailWord_5832519
  simp only [CollatzResearch.WordTrace]
  refine ⟨212729444356787252785548611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141819629571191501857032407 212729444356787252785548611)
  ·
    refine ⟨319094166535180879178322917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212729444356787252785548611 319094166535180879178322917)
    ·
      refine ⟨59830156225346414845935547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319094166535180879178322917 59830156225346414845935547)
      ·
        refine ⟨89745234338019622268903321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59830156225346414845935547 89745234338019622268903321)
        ·
          refine ⟨67308925753514716701677491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89745234338019622268903321 67308925753514716701677491)
          ·
            refine ⟨100963388630272075052516237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67308925753514716701677491 100963388630272075052516237)
            ·
              refine ⟨37861270736352028144693589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100963388630272075052516237 37861270736352028144693589)
              ·
                refine ⟨110921691610406332455157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37861270736352028144693589 110921691610406332455157)
                ·
                  rfl

theorem cell23_5832519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 10].length) (baseStart_5832519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832519 prefixEnd_5832519 := by exact prefixLift 5832519
  have htrace : WordTrace (prefixWord ++ tailWord_5832519) baseStart_5832519 baseEnd_5832519 := by
    simpa [prefixWord, tailWord_5832519, baseEnd_5832519] using wordTrace_append hprefix tailTrace_5832519
  have hstable : (prefixWord ++ tailWord_5832519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832519).length < 2 ^ (prefixWord ++ tailWord_5832519).sum := by decide
  have hdescent : baseEnd_5832519 < baseStart_5832519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832530 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_5832530 : Nat := 118140960795 + 5832530 * 2 ^ 59
def prefixEnd_5832530 : Nat := 4983230072969 + 3 ^ 40 * 5832530 * 2
def baseEnd_5832530 : Nat := 2994891321768170433251689

theorem tailTrace_5832530 : CollatzResearch.WordTrace tailWord_5832530 prefixEnd_5832530 2994891321768170433251689 := by
  unfold tailWord_5832530
  simp only [CollatzResearch.WordTrace]
  refine ⟨53182461389936850416049761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141819897039831601109466029 53182461389936850416049761)
  ·
    refine ⟨39886846042452637812037321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53182461389936850416049761 39886846042452637812037321)
    ·
      refine ⟨29915134531839478359027991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39886846042452637812037321 29915134531839478359027991)
      ·
        refine ⟨44872701797759217538541987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29915134531839478359027991 44872701797759217538541987)
        ·
          refine ⟨67309052696638826307812981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44872701797759217538541987 67309052696638826307812981)
          ·
            refine ⟨6310223690309889966357467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67309052696638826307812981 6310223690309889966357467)
            ·
              refine ⟨9465335535464834949536201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310223690309889966357467 9465335535464834949536201)
              ·
                refine ⟨7099001651598626212152151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9465335535464834949536201 7099001651598626212152151)
                ·
                  refine ⟨10648502477397939318228227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099001651598626212152151 10648502477397939318228227)
                  ·
                    refine ⟨15972753716096908977342341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10648502477397939318228227 15972753716096908977342341)
                    ·
                      refine ⟨2994891321768170433251689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15972753716096908977342341 2994891321768170433251689)
                      ·
                        rfl

theorem cell23_5832530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_5832530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832530 prefixEnd_5832530 := by exact prefixLift 5832530
  have htrace : WordTrace (prefixWord ++ tailWord_5832530) baseStart_5832530 baseEnd_5832530 := by
    simpa [prefixWord, tailWord_5832530, baseEnd_5832530] using wordTrace_append hprefix tailTrace_5832530
  have hstable : (prefixWord ++ tailWord_5832530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832530).length < 2 ^ (prefixWord ++ tailWord_5832530).sum := by decide
  have hdescent : baseEnd_5832530 < baseStart_5832530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832533 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5832533 : Nat := 118140960795 + 5832533 * 2 ^ 59
def prefixEnd_5832533 : Nat := 4983230072969 + 3 ^ 40 * 5832533 * 2
def baseEnd_5832533 : Nat := 2994892862210133921514175

theorem tailTrace_5832533 : CollatzResearch.WordTrace tailWord_5832533 prefixEnd_5832533 2994892862210133921514175 := by
  unfold tailWord_5832533
  simp only [CollatzResearch.WordTrace]
  refine ⟨212729954978736533176558253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141819969985824355451038835 212729954978736533176558253)
  ·
    refine ⟨79773733117026199941209345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212729954978736533176558253 79773733117026199941209345)
    ·
      refine ⟨59830299837769649955907009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79773733117026199941209345 59830299837769649955907009)
      ·
        refine ⟨44872724878327237466930257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59830299837769649955907009 44872724878327237466930257)
        ·
          refine ⟨33654543658745428100197693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44872724878327237466930257 33654543658745428100197693)
          ·
            refine ⟨12620453872029535537574135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33654543658745428100197693 12620453872029535537574135)
            ·
              refine ⟨18930680808044303306361203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12620453872029535537574135 18930680808044303306361203)
              ·
                refine ⟨28396021212066454959541805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18930680808044303306361203 28396021212066454959541805)
                ·
                  refine ⟨10648507954524920609828177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28396021212066454959541805 10648507954524920609828177)
                  ·
                    refine ⟨7986380965893690457371133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10648507954524920609828177 7986380965893690457371133)
                    ·
                      refine ⟨2994892862210133921514175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986380965893690457371133 2994892862210133921514175)
                      ·
                        rfl

theorem cell23_5832533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5832533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832533 prefixEnd_5832533 := by exact prefixLift 5832533
  have htrace : WordTrace (prefixWord ++ tailWord_5832533) baseStart_5832533 baseEnd_5832533 := by
    simpa [prefixWord, tailWord_5832533, baseEnd_5832533] using wordTrace_append hprefix tailTrace_5832533
  have hstable : (prefixWord ++ tailWord_5832533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832533).length < 2 ^ (prefixWord ++ tailWord_5832533).sum := by decide
  have hdescent : baseEnd_5832533 < baseStart_5832533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832559 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_5832559 : Nat := 118140960795 + 5832559 * 2 ^ 59
def prefixEnd_5832559 : Nat := 4983230072969 + 3 ^ 40 * 5832559 * 2
def baseEnd_5832559 : Nat := 2994906212707150819789055

theorem tailTrace_5832559 : CollatzResearch.WordTrace tailWord_5832559 prefixEnd_5832559 2994906212707150819789055 := by
  unfold tailWord_5832559
  simp only [CollatzResearch.WordTrace]
  refine ⟨212730903276642339617004731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141820602184428226411336487 212730903276642339617004731)
  ·
    refine ⟨319096354914963509425507097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212730903276642339617004731 319096354914963509425507097)
    ·
      refine ⟨239322266186222632069130323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319096354914963509425507097 239322266186222632069130323)
      ·
        refine ⟨358983399279333948103695485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239322266186222632069130323 358983399279333948103695485)
        ·
          refine ⟨134618774729750230538885807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358983399279333948103695485 134618774729750230538885807)
          ·
            refine ⟨201928162094625345808328711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134618774729750230538885807 201928162094625345808328711)
            ·
              refine ⟨302892243141938018712493067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201928162094625345808328711 302892243141938018712493067)
              ·
                refine ⟨454338364712907028068739601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302892243141938018712493067 454338364712907028068739601)
                ·
                  refine ⟨340753773534680271051554701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454338364712907028068739601 340753773534680271051554701)
                  ·
                    refine ⟨127782665075505101644333013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340753773534680271051554701 127782665075505101644333013)
                    ·
                      refine ⟨2994906212707150819789055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127782665075505101644333013 2994906212707150819789055)
                      ·
                        rfl

theorem cell23_5832559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_5832559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832559 prefixEnd_5832559 := by exact prefixLift 5832559
  have htrace : WordTrace (prefixWord ++ tailWord_5832559) baseStart_5832559 baseEnd_5832559 := by
    simpa [prefixWord, tailWord_5832559, baseEnd_5832559] using wordTrace_append hprefix tailTrace_5832559
  have hstable : (prefixWord ++ tailWord_5832559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832559).length < 2 ^ (prefixWord ++ tailWord_5832559).sum := by decide
  have hdescent : baseEnd_5832559 < baseStart_5832559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832580 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5832580 : Nat := 118140960795 + 5832580 * 2 ^ 59
def prefixEnd_5832580 : Nat := 4983230072969 + 3 ^ 40 * 5832580 * 2
def baseEnd_5832580 : Nat := 2994916995800895237626459

theorem tailTrace_5832580 : CollatzResearch.WordTrace tailWord_5832580 prefixEnd_5832580 2994916995800895237626459 := by
  unfold tailWord_5832580
  simp only [CollatzResearch.WordTrace]
  refine ⟨106365834604783130101759597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141821112806377506802346129 106365834604783130101759597)
  ·
    refine ⟨39887187976793673788159849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106365834604783130101759597 39887187976793673788159849)
    ·
      refine ⟨29915390982595255341119887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39887187976793673788159849 29915390982595255341119887)
      ·
        refine ⟨44873086473892883011679831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29915390982595255341119887 44873086473892883011679831)
        ·
          refine ⟨67309629710839324517519747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44873086473892883011679831 67309629710839324517519747)
          ·
            refine ⟨100964444566258986776279621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67309629710839324517519747 100964444566258986776279621)
            ·
              refine ⟨18930833356173560020552429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100964444566258986776279621 18930833356173560020552429)
              ·
                refine ⟨7099062508565085007707161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18930833356173560020552429 7099062508565085007707161)
                ·
                  refine ⟨5324296881423813755780371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099062508565085007707161 5324296881423813755780371)
                  ·
                    refine ⟨7986445322135720633670557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5324296881423813755780371 7986445322135720633670557)
                    ·
                      refine ⟨2994916995800895237626459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986445322135720633670557 2994916995800895237626459)
                      ·
                        rfl

theorem cell23_5832580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5832580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832580 prefixEnd_5832580 := by exact prefixLift 5832580
  have htrace : WordTrace (prefixWord ++ tailWord_5832580) baseStart_5832580 baseEnd_5832580 := by
    simpa [prefixWord, tailWord_5832580, baseEnd_5832580] using wordTrace_append hprefix tailTrace_5832580
  have hstable : (prefixWord ++ tailWord_5832580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832580).length < 2 ^ (prefixWord ++ tailWord_5832580).sum := by decide
  have hdescent : baseEnd_5832580 < baseStart_5832580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832598 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5832598 : Nat := 118140960795 + 5832598 * 2 ^ 59
def prefixEnd_5832598 : Nat := 4983230072969 + 3 ^ 40 * 5832598 * 2
def baseEnd_5832598 : Nat := 2994926238452676167201377

theorem tailTrace_5832598 : CollatzResearch.WordTrace tailWord_5832598 prefixEnd_5832598 2994926238452676167201377 := by
  unfold tailWord_5832598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295770357718815579854653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141821550482334032851782965 13295770357718815579854653)
  ·
    refine ⟨4985913884144555842445495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13295770357718815579854653 4985913884144555842445495)
    ·
      refine ⟨7478870826216833763668243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985913884144555842445495 7478870826216833763668243)
      ·
        refine ⟨11218306239325250645502365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7478870826216833763668243 11218306239325250645502365)
        ·
          refine ⟨4206864839746968992063387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11218306239325250645502365 4206864839746968992063387)
          ·
            refine ⟨6310297259620453488095081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206864839746968992063387 6310297259620453488095081)
            ·
              refine ⟨4732722944715340116071311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6310297259620453488095081 4732722944715340116071311)
              ·
                refine ⟨7099084417073010174106967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732722944715340116071311 7099084417073010174106967)
                ·
                  refine ⟨10648626625609515261160451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099084417073010174106967 10648626625609515261160451)
                  ·
                    refine ⟨15972939938414272891740677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10648626625609515261160451 15972939938414272891740677)
                    ·
                      refine ⟨2994926238452676167201377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15972939938414272891740677 2994926238452676167201377)
                      ·
                        rfl

theorem cell23_5832598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5832598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832598 prefixEnd_5832598 := by exact prefixLift 5832598
  have htrace : WordTrace (prefixWord ++ tailWord_5832598) baseStart_5832598 baseEnd_5832598 := by
    simpa [prefixWord, tailWord_5832598, baseEnd_5832598] using wordTrace_append hprefix tailTrace_5832598
  have hstable : (prefixWord ++ tailWord_5832598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832598).length < 2 ^ (prefixWord ++ tailWord_5832598).sum := by decide
  have hdescent : baseEnd_5832598 < baseStart_5832598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832607 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 1, 3, 2]
def baseStart_5832607 : Nat := 118140960795 + 5832607 * 2 ^ 59
def prefixEnd_5832607 : Nat := 4983230072969 + 3 ^ 40 * 5832607 * 2
def baseEnd_5832607 : Nat := 2994930859778566631988835

theorem tailTrace_5832607 : CollatzResearch.WordTrace tailWord_5832607 prefixEnd_5832607 2994930859778566631988835 := by
  unfold tailWord_5832607
  simp only [CollatzResearch.WordTrace]
  refine ⟨212732653980468443814752075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141821769320312295876501383 212732653980468443814752075)
  ·
    refine ⟨319098980970702665722128113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212732653980468443814752075 319098980970702665722128113)
    ·
      refine ⟨239324235728026999291596085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319098980970702665722128113 239324235728026999291596085)
      ·
        refine ⟨22436647099502531183587133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239324235728026999291596085 22436647099502531183587133)
        ·
          refine ⟨8413742662313449193845175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22436647099502531183587133 8413742662313449193845175)
          ·
            refine ⟨12620613993470173790767763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8413742662313449193845175 12620613993470173790767763)
            ·
              refine ⟨18930920990205260686151645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12620613993470173790767763 18930920990205260686151645)
              ·
                refine ⟨7099095371326972757306867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18930920990205260686151645 7099095371326972757306867)
                ·
                  refine ⟨10648643056990459135960301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099095371326972757306867 10648643056990459135960301)
                  ·
                    refine ⟨3993241146371422175985113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10648643056990459135960301 3993241146371422175985113)
                    ·
                      refine ⟨2994930859778566631988835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993241146371422175985113 2994930859778566631988835)
                      ·
                        rfl

theorem cell23_5832607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_5832607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832607 prefixEnd_5832607 := by exact prefixLift 5832607
  have htrace : WordTrace (prefixWord ++ tailWord_5832607) baseStart_5832607 baseEnd_5832607 := by
    simpa [prefixWord, tailWord_5832607, baseEnd_5832607] using wordTrace_append hprefix tailTrace_5832607
  have hstable : (prefixWord ++ tailWord_5832607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832607).length < 2 ^ (prefixWord ++ tailWord_5832607).sum := by decide
  have hdescent : baseEnd_5832607 < baseStart_5832607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832637 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5832637 : Nat := 118140960795 + 5832637 * 2 ^ 59
def prefixEnd_5832637 : Nat := 4983230072969 + 3 ^ 40 * 5832637 * 2
def baseEnd_5832637 : Nat := 2994946264198201514613697

theorem tailTrace_5832637 : CollatzResearch.WordTrace tailWord_5832637 prefixEnd_5832637 2994946264198201514613697 := by
  unfold tailWord_5832637
  simp only [CollatzResearch.WordTrace]
  refine ⟨212733748170359758938344165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141822498780239839292229443 212733748170359758938344165)
  ·
    refine ⟨39887577781942454800939531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212733748170359758938344165 39887577781942454800939531)
    ·
      refine ⟨59831366672913682201409297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39887577781942454800939531 59831366672913682201409297)
      ·
        refine ⟨44873525004685261651056973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59831366672913682201409297 44873525004685261651056973)
        ·
          refine ⟨16827571876756973119146365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44873525004685261651056973 16827571876756973119146365)
          ·
            refine ⟨6310339453783864919679887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16827571876756973119146365 6310339453783864919679887)
            ·
              refine ⟨9465509180675797379519831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310339453783864919679887 9465509180675797379519831)
              ·
                refine ⟨14198263771013696069279747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9465509180675797379519831 14198263771013696069279747)
                ·
                  refine ⟨21297395656520544103919621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14198263771013696069279747 21297395656520544103919621)
                  ·
                    refine ⟨3993261685597602019484929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21297395656520544103919621 3993261685597602019484929)
                    ·
                      refine ⟨2994946264198201514613697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993261685597602019484929 2994946264198201514613697)
                      ·
                        rfl

theorem cell23_5832637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5832637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832637 prefixEnd_5832637 := by exact prefixLift 5832637
  have htrace : WordTrace (prefixWord ++ tailWord_5832637) baseStart_5832637 baseEnd_5832637 := by
    simpa [prefixWord, tailWord_5832637, baseEnd_5832637] using wordTrace_append hprefix tailTrace_5832637
  have hstable : (prefixWord ++ tailWord_5832637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832637).length < 2 ^ (prefixWord ++ tailWord_5832637).sum := by decide
  have hdescent : baseEnd_5832637 < baseStart_5832637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832656 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_5832656 : Nat := 118140960795 + 5832656 * 2 ^ 59
def prefixEnd_5832656 : Nat := 4983230072969 + 3 ^ 40 * 5832656 * 2
def baseEnd_5832656 : Nat := 998318673443545646758703

theorem tailTrace_5832656 : CollatzResearch.WordTrace tailWord_5832656 prefixEnd_5832656 998318673443545646758703 := by
  unfold tailWord_5832656
  simp only [CollatzResearch.WordTrace]
  refine ⟨106367220578645462591642911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141822960771527283455523881 106367220578645462591642911)
  ·
    refine ⟨159550830867968193887464367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106367220578645462591642911 159550830867968193887464367)
    ·
      refine ⟨239326246301952290831196551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159550830867968193887464367 239326246301952290831196551)
      ·
        refine ⟨358989369452928436246794827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239326246301952290831196551 358989369452928436246794827)
        ·
          refine ⟨538484054179392654370192241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358989369452928436246794827 538484054179392654370192241)
          ·
            refine ⟨403863040634544490777644181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538484054179392654370192241 403863040634544490777644181)
            ·
              refine ⟨18931080029744273005202071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403863040634544490777644181 18931080029744273005202071)
              ·
                refine ⟨28396620044616409507803107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18931080029744273005202071 28396620044616409507803107)
                ·
                  refine ⟨42594930066924614261704661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28396620044616409507803107 42594930066924614261704661)
                  ·
                    refine ⟨998318673443545646758703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42594930066924614261704661 998318673443545646758703)
                    ·
                      rfl

theorem cell23_5832656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_5832656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832656 prefixEnd_5832656 := by exact prefixLift 5832656
  have htrace : WordTrace (prefixWord ++ tailWord_5832656) baseStart_5832656 baseEnd_5832656 := by
    simpa [prefixWord, tailWord_5832656, baseEnd_5832656] using wordTrace_append hprefix tailTrace_5832656
  have hstable : (prefixWord ++ tailWord_5832656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832656).length < 2 ^ (prefixWord ++ tailWord_5832656).sum := by decide
  have hdescent : baseEnd_5832656 < baseStart_5832656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832703 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 3, 4]
def baseStart_5832703 : Nat := 118140960795 + 5832703 * 2 ^ 59
def prefixEnd_5832703 : Nat := 4983230072969 + 3 ^ 40 * 5832703 * 2
def baseEnd_5832703 : Nat := 998326717973799418796131

theorem tailTrace_5832703 : CollatzResearch.WordTrace tailWord_5832703 prefixEnd_5832703 998326717973799418796131 := by
  unfold tailWord_5832703
  simp only [CollatzResearch.WordTrace]
  refine ⟨212736155388120652210246763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141824103592080434806831175 212736155388120652210246763)
  ·
    refine ⟨319104233082180978315370145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212736155388120652210246763 319104233082180978315370145)
    ·
      refine ⟨239328174811635733736527609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319104233082180978315370145 239328174811635733736527609)
      ·
        refine ⟨179496131108726800302395707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239328174811635733736527609 179496131108726800302395707)
        ·
          refine ⟨269244196663090200453593561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179496131108726800302395707 269244196663090200453593561)
          ·
            refine ⟨201933147497317650340195171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269244196663090200453593561 201933147497317650340195171)
            ·
              refine ⟨302899721245976475510292757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201933147497317650340195171 302899721245976475510292757)
              ·
                refine ⟨14198424433405147289544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302899721245976475510292757 14198424433405147289544973)
                ·
                  refine ⟨5324409162526930233579365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14198424433405147289544973 5324409162526930233579365)
                  ·
                    refine ⟨998326717973799418796131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324409162526930233579365 998326717973799418796131)
                    ·
                      rfl

theorem cell23_5832703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_5832703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832703 prefixEnd_5832703 := by exact prefixLift 5832703
  have htrace : WordTrace (prefixWord ++ tailWord_5832703) baseStart_5832703 baseEnd_5832703 := by
    simpa [prefixWord, tailWord_5832703, baseEnd_5832703] using wordTrace_append hprefix tailTrace_5832703
  have hstable : (prefixWord ++ tailWord_5832703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832703).length < 2 ^ (prefixWord ++ tailWord_5832703).sum := by decide
  have hdescent : baseEnd_5832703 < baseStart_5832703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832730 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_5832730 : Nat := 118140960795 + 5832730 * 2 ^ 59
def prefixEnd_5832730 : Nat := 4983230072969 + 3 ^ 40 * 5832730 * 2
def baseEnd_5832730 : Nat := 2994994017899069650750769

theorem tailTrace_5832730 : CollatzResearch.WordTrace tailWord_5832730 prefixEnd_5832730 2994994017899069650750769 := by
  unfold tailWord_5832730
  simp only [CollatzResearch.WordTrace]
  refine ⟨53184285039755708955369911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141824760106015223880986429 53184285039755708955369911)
  ·
    refine ⟨79776427559633563433054867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53184285039755708955369911 79776427559633563433054867)
    ·
      refine ⟨119664641339450345149582301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79776427559633563433054867 119664641339450345149582301)
      ·
        refine ⟨44874240502293879431093363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119664641339450345149582301 44874240502293879431093363)
        ·
          refine ⟨67311360753440819146640045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44874240502293879431093363 67311360753440819146640045)
          ·
            refine ⟨25241760282540307179990017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67311360753440819146640045 25241760282540307179990017)
            ·
              refine ⟨18931320211905230384992513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25241760282540307179990017 18931320211905230384992513)
              ·
                refine ⟨14198490158928922788744385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18931320211905230384992513 14198490158928922788744385)
                ·
                  refine ⟨10648867619196692091558289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14198490158928922788744385 10648867619196692091558289)
                  ·
                    refine ⟨7986650714397519068668717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10648867619196692091558289 7986650714397519068668717)
                    ·
                      refine ⟨2994994017899069650750769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986650714397519068668717 2994994017899069650750769)
                      ·
                        rfl

theorem cell23_5832730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_5832730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832730 prefixEnd_5832730 := by exact prefixLift 5832730
  have htrace : WordTrace (prefixWord ++ tailWord_5832730) baseStart_5832730 baseEnd_5832730 := by
    simpa [prefixWord, tailWord_5832730, baseEnd_5832730] using wordTrace_append hprefix tailTrace_5832730
  have hstable : (prefixWord ++ tailWord_5832730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832730).length < 2 ^ (prefixWord ++ tailWord_5832730).sum := by decide
  have hdescent : baseEnd_5832730 < baseStart_5832730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832744 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5832744 : Nat := 118140960795 + 5832744 * 2 ^ 59
def prefixEnd_5832744 : Nat := 4983230072969 + 3 ^ 40 * 5832744 * 2
def baseEnd_5832744 : Nat := 2995001206628232595975705

theorem tailTrace_5832744 : CollatzResearch.WordTrace tailWord_5832744 prefixEnd_5832744 2995001206628232595975705 := by
  unfold tailWord_5832744
  simp only [CollatzResearch.WordTrace]
  refine ⟨106368825390486058106244643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141825100520648077474992857 106368825390486058106244643)
  ·
    refine ⟨159553238085729087159366965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106368825390486058106244643 159553238085729087159366965)
    ·
      refine ⟨14958116070537101921190653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159553238085729087159366965 14958116070537101921190653)
      ·
        refine ⟨5609293526451413220446495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14958116070537101921190653 5609293526451413220446495)
        ·
          refine ⟨8413940289677119830669743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609293526451413220446495 8413940289677119830669743)
          ·
            refine ⟨12620910434515679746004615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8413940289677119830669743 12620910434515679746004615)
            ·
              refine ⟨18931365651773519619006923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12620910434515679746004615 18931365651773519619006923)
              ·
                refine ⟨28397048477660279428510385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18931365651773519619006923 28397048477660279428510385)
                ·
                  refine ⟨21297786358245209571382789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28397048477660279428510385 21297786358245209571382789)
                  ·
                    refine ⟨3993334942170976794634273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21297786358245209571382789 3993334942170976794634273)
                    ·
                      refine ⟨2995001206628232595975705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993334942170976794634273 2995001206628232595975705)
                      ·
                        rfl

theorem cell23_5832744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5832744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832744 prefixEnd_5832744 := by exact prefixLift 5832744
  have htrace : WordTrace (prefixWord ++ tailWord_5832744) baseStart_5832744 baseEnd_5832744 := by
    simpa [prefixWord, tailWord_5832744, baseEnd_5832744] using wordTrace_append hprefix tailTrace_5832744
  have hstable : (prefixWord ++ tailWord_5832744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832744).length < 2 ^ (prefixWord ++ tailWord_5832744).sum := by decide
  have hdescent : baseEnd_5832744 < baseStart_5832744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832750 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_5832750 : Nat := 118140960795 + 5832750 * 2 ^ 59
def prefixEnd_5832750 : Nat := 4983230072969 + 3 ^ 40 * 5832750 * 2
def baseEnd_5832750 : Nat := 332778254168017730277853

theorem tailTrace_5832750 : CollatzResearch.WordTrace tailWord_5832750 prefixEnd_5832750 332778254168017730277853 := by
  unfold tailWord_5832750
  simp only [CollatzResearch.WordTrace]
  refine ⟨26592233702368797404650963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141825246412633586158138469 26592233702368797404650963)
  ·
    refine ⟨39888350553553196106976445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26592233702368797404650963 39888350553553196106976445)
    ·
      refine ⟨14958131457582448540116167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39888350553553196106976445 14958131457582448540116167)
      ·
        refine ⟨22437197186373672810174251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14958131457582448540116167 22437197186373672810174251)
        ·
          refine ⟨33655795779560509215261377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22437197186373672810174251 33655795779560509215261377)
          ·
            refine ⟨25241846834670381911446033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33655795779560509215261377 25241846834670381911446033)
            ·
              refine ⟨18931385126002786433584525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25241846834670381911446033 18931385126002786433584525)
              ·
                refine ⟨7099269422251044912594197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18931385126002786433584525 7099269422251044912594197)
                ·
                  refine ⟨332778254168017730277853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7099269422251044912594197 332778254168017730277853)
                  ·
                    rfl

theorem cell23_5832750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_5832750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832750 prefixEnd_5832750 := by exact prefixLift 5832750
  have htrace : WordTrace (prefixWord ++ tailWord_5832750) baseStart_5832750 baseEnd_5832750 := by
    simpa [prefixWord, tailWord_5832750, baseEnd_5832750] using wordTrace_append hprefix tailTrace_5832750
  have hstable : (prefixWord ++ tailWord_5832750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832750).length < 2 ^ (prefixWord ++ tailWord_5832750).sum := by decide
  have hdescent : baseEnd_5832750 < baseStart_5832750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832803 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5832803 : Nat := 118140960795 + 5832803 * 2 ^ 59
def prefixEnd_5832803 : Nat := 4983230072969 + 3 ^ 40 * 5832803 * 2
def baseEnd_5832803 : Nat := 2995031501986847865137933

theorem tailTrace_5832803 : CollatzResearch.WordTrace tailWord_5832803 prefixEnd_5832803 2995031501986847865137933 := by
  unfold tailWord_5832803
  simp only [CollatzResearch.WordTrace]
  refine ⟨212739802687758369288887063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141826535125172246192591375 212739802687758369288887063)
  ·
    refine ⟨319109704031637553933330595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212739802687758369288887063 319109704031637553933330595)
    ·
      refine ⟨478664556047456330899995893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319109704031637553933330595 478664556047456330899995893)
      ·
        refine ⟨44874802129449031021874615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 478664556047456330899995893 44874802129449031021874615)
        ·
          refine ⟨67312203194173546532811923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44874802129449031021874615 67312203194173546532811923)
          ·
            refine ⟨100968304791260319799217885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67312203194173546532811923 100968304791260319799217885)
            ·
              refine ⟨37863114296722619924706707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100968304791260319799217885 37863114296722619924706707)
              ·
                refine ⟨56794671445083929887060061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37863114296722619924706707 56794671445083929887060061)
                ·
                  refine ⟨21298001791906473707647523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56794671445083929887060061 21298001791906473707647523)
                  ·
                    refine ⟨31947002687859710561471285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21298001791906473707647523 31947002687859710561471285)
                    ·
                      refine ⟨2995031501986847865137933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31947002687859710561471285 2995031501986847865137933)
                      ·
                        rfl

theorem cell23_5832803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5832803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832803 prefixEnd_5832803 := by exact prefixLift 5832803
  have htrace : WordTrace (prefixWord ++ tailWord_5832803) baseStart_5832803 baseEnd_5832803 := by
    simpa [prefixWord, tailWord_5832803, baseEnd_5832803] using wordTrace_append hprefix tailTrace_5832803
  have hstable : (prefixWord ++ tailWord_5832803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832803).length < 2 ^ (prefixWord ++ tailWord_5832803).sum := by decide
  have hdescent : baseEnd_5832803 < baseStart_5832803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832817 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_5832817 : Nat := 118140960795 + 5832817 * 2 ^ 59
def prefixEnd_5832817 : Nat := 4983230072969 + 3 ^ 40 * 5832817 * 2
def baseEnd_5832817 : Nat := 2995038690716010810362869

theorem tailTrace_5832817 : CollatzResearch.WordTrace tailWord_5832817 prefixEnd_5832817 2995038690716010810362869 := by
  unfold tailWord_5832817
  simp only [CollatzResearch.WordTrace]
  refine ⟨212740313309707649679896705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141826875539805099786597803 212740313309707649679896705)
  ·
    refine ⟨159555234982280737259922529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212740313309707649679896705 159555234982280737259922529)
    ·
      refine ⟨119666426236710552944941897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159555234982280737259922529 119666426236710552944941897)
      ·
        refine ⟨89749819677532914708706423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119666426236710552944941897 89749819677532914708706423)
        ·
          refine ⟨134624729516299372063059635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89749819677532914708706423 134624729516299372063059635)
          ·
            refine ⟨201937094274449058094589453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134624729516299372063059635 201937094274449058094589453)
            ·
              refine ⟨75726410352918396785471045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201937094274449058094589453 75726410352918396785471045)
              ·
                refine ⟨14198701941172199397275821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75726410352918396785471045 14198701941172199397275821)
                ·
                  refine ⟨5324513227939574773978433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14198701941172199397275821 5324513227939574773978433)
                  ·
                    refine ⟨3993384920954681080483825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324513227939574773978433 3993384920954681080483825)
                    ·
                      refine ⟨2995038690716010810362869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993384920954681080483825 2995038690716010810362869)
                      ·
                        rfl

theorem cell23_5832817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_5832817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832817 prefixEnd_5832817 := by exact prefixLift 5832817
  have htrace : WordTrace (prefixWord ++ tailWord_5832817) baseStart_5832817 baseEnd_5832817 := by
    simpa [prefixWord, tailWord_5832817, baseEnd_5832817] using wordTrace_append hprefix tailTrace_5832817
  have hstable : (prefixWord ++ tailWord_5832817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832817).length < 2 ^ (prefixWord ++ tailWord_5832817).sum := by decide
  have hdescent : baseEnd_5832817 < baseStart_5832817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832823 : List Nat := [1, 1, 3, 1, 1, 6, 1, 9]
def baseStart_5832823 : Nat := 118140960795 + 5832823 * 2 ^ 59
def prefixEnd_5832823 : Nat := 4983230072969 + 3 ^ 40 * 5832823 * 2
def baseEnd_5832823 : Nat := 110927473022219918032883

theorem tailTrace_5832823 : CollatzResearch.WordTrace tailWord_5832823 prefixEnd_5832823 110927473022219918032883 := by
  unfold tailWord_5832823
  simp only [CollatzResearch.WordTrace]
  refine ⟨212740532147685912704615123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141827021431790608469743415 212740532147685912704615123)
  ·
    refine ⟨319110798221528869056922685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212740532147685912704615123 319110798221528869056922685)
    ·
      refine ⟨119666549333073325896346007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319110798221528869056922685 119666549333073325896346007)
      ·
        refine ⟨179499823999609988844519011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119666549333073325896346007 179499823999609988844519011)
        ·
          refine ⟨269249735999414983266778517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179499823999609988844519011 269249735999414983266778517)
          ·
            refine ⟨12621081374972577340630243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269249735999414983266778517 12621081374972577340630243)
            ·
              refine ⟨18931622062458866010945365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621081374972577340630243 18931622062458866010945365)
              ·
                refine ⟨110927473022219918032883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18931622062458866010945365 110927473022219918032883)
                ·
                  rfl

theorem cell23_5832823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 9].length) (baseStart_5832823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832823 prefixEnd_5832823 := by exact prefixLift 5832823
  have htrace : WordTrace (prefixWord ++ tailWord_5832823) baseStart_5832823 baseEnd_5832823 := by
    simpa [prefixWord, tailWord_5832823, baseEnd_5832823] using wordTrace_append hprefix tailTrace_5832823
  have hstable : (prefixWord ++ tailWord_5832823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832823).length < 2 ^ (prefixWord ++ tailWord_5832823).sum := by decide
  have hdescent : baseEnd_5832823 < baseStart_5832823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832837 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_5832837 : Nat := 118140960795 + 5832837 * 2 ^ 59
def prefixEnd_5832837 : Nat := 4983230072969 + 3 ^ 40 * 5832837 * 2
def baseEnd_5832837 : Nat := 2995048960329100732112777

theorem tailTrace_5832837 : CollatzResearch.WordTrace tailWord_5832837 prefixEnd_5832837 2995048960329100732112777 := by
  unfold tailWord_5832837
  simp only [CollatzResearch.WordTrace]
  refine ⟨212741042769635193095624765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141827361846423462063749843 212741042769635193095624765)
  ·
    refine ⟨79777891038613197410859287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212741042769635193095624765 79777891038613197410859287)
    ·
      refine ⟨119666836557919796116288931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79777891038613197410859287 119666836557919796116288931)
      ·
        refine ⟨179500254836879694174433397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119666836557919796116288931 179500254836879694174433397)
        ·
          refine ⟨16828148890957471328853131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179500254836879694174433397 16828148890957471328853131)
          ·
            refine ⟨25242223336436206993279697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16828148890957471328853131 25242223336436206993279697)
            ·
              refine ⟨18931667502327155244959773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25242223336436206993279697 18931667502327155244959773)
              ·
                refine ⟨7099375313372683216859915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18931667502327155244959773 7099375313372683216859915)
                ·
                  refine ⟨10649062970059024825289873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099375313372683216859915 10649062970059024825289873)
                  ·
                    refine ⟨7986797227544268618967405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10649062970059024825289873 7986797227544268618967405)
                    ·
                      refine ⟨2995048960329100732112777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986797227544268618967405 2995048960329100732112777)
                      ·
                        rfl

theorem cell23_5832837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_5832837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832837 prefixEnd_5832837 := by exact prefixLift 5832837
  have htrace : WordTrace (prefixWord ++ tailWord_5832837) baseStart_5832837 baseEnd_5832837 := by
    simpa [prefixWord, tailWord_5832837, baseEnd_5832837] using wordTrace_append hprefix tailTrace_5832837
  have hstable : (prefixWord ++ tailWord_5832837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832837).length < 2 ^ (prefixWord ++ tailWord_5832837).sum := by decide
  have hdescent : baseEnd_5832837 < baseStart_5832837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832840 : List Nat := [2, 1, 3, 4, 1, 3, 9]
def baseStart_5832840 : Nat := 118140960795 + 5832840 * 2 ^ 59
def prefixEnd_5832840 : Nat := 4983230072969 + 3 ^ 40 * 5832840 * 2
def baseEnd_5832840 : Nat := 36975932108284743461423

theorem tailTrace_5832840 : CollatzResearch.WordTrace tailWord_5832840 prefixEnd_5832840 36975932108284743461423 := by
  unfold tailWord_5832840
  simp only [CollatzResearch.WordTrace]
  refine ⟨106370576094312162303991987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141827434792416216405322649 106370576094312162303991987)
  ·
    refine ⟨159555864141468243455987981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106370576094312162303991987 159555864141468243455987981)
    ·
      refine ⟨59833449053050591295995493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159555864141468243455987981 59833449053050591295995493)
      ·
        refine ⟨11218771697446985867999155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59833449053050591295995493 11218771697446985867999155)
        ·
          refine ⟨16828157546170478801998733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11218771697446985867999155 16828157546170478801998733)
          ·
            refine ⟨6310559079813929550749525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16828157546170478801998733 6310559079813929550749525)
            ·
              refine ⟨36975932108284743461423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6310559079813929550749525 36975932108284743461423)
              ·
                rfl

theorem cell23_5832840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 9].length) (baseStart_5832840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832840 prefixEnd_5832840 := by exact prefixLift 5832840
  have htrace : WordTrace (prefixWord ++ tailWord_5832840) baseStart_5832840 baseEnd_5832840 := by
    simpa [prefixWord, tailWord_5832840, baseEnd_5832840] using wordTrace_append hprefix tailTrace_5832840
  have hstable : (prefixWord ++ tailWord_5832840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832840).length < 2 ^ (prefixWord ++ tailWord_5832840).sum := by decide
  have hdescent : baseEnd_5832840 < baseStart_5832840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832853 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_5832853 : Nat := 118140960795 + 5832853 * 2 ^ 59
def prefixEnd_5832853 : Nat := 4983230072969 + 3 ^ 40 * 5832853 * 2
def baseEnd_5832853 : Nat := 998352392006524223170901

theorem tailTrace_5832853 : CollatzResearch.WordTrace tailWord_5832853 prefixEnd_5832853 998352392006524223170901 := by
  unfold tailWord_5832853
  simp only [CollatzResearch.WordTrace]
  refine ⟨212741626337577227828207213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141827750891718151885471475 212741626337577227828207213)
  ·
    refine ⟨79778109876591460435577705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212741626337577227828207213 79778109876591460435577705)
    ·
      refine ⟨59833582407443595326683279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79778109876591460435577705 59833582407443595326683279)
      ·
        refine ⟨89750373611165392990024919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59833582407443595326683279 89750373611165392990024919)
        ·
          refine ⟨134625560416748089485037379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89750373611165392990024919 134625560416748089485037379)
          ·
            refine ⟨201938340625122134227556069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134625560416748089485037379 201938340625122134227556069)
            ·
              refine ⟨37863438867210400167666763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201938340625122134227556069 37863438867210400167666763)
              ·
                refine ⟨56795158300815600251500145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37863438867210400167666763 56795158300815600251500145)
                ·
                  refine ⟨42596368725611700188625109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56795158300815600251500145 42596368725611700188625109)
                  ·
                    refine ⟨998352392006524223170901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42596368725611700188625109 998352392006524223170901)
                    ·
                      rfl

theorem cell23_5832853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_5832853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832853 prefixEnd_5832853 := by exact prefixLift 5832853
  have htrace : WordTrace (prefixWord ++ tailWord_5832853) baseStart_5832853 baseEnd_5832853 := by
    simpa [prefixWord, tailWord_5832853, baseEnd_5832853] using wordTrace_append hprefix tailTrace_5832853
  have hstable : (prefixWord ++ tailWord_5832853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832853).length < 2 ^ (prefixWord ++ tailWord_5832853).sum := by decide
  have hdescent : baseEnd_5832853 < baseStart_5832853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832871 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5832871 : Nat := 118140960795 + 5832871 * 2 ^ 59
def prefixEnd_5832871 : Nat := 4983230072969 + 3 ^ 40 * 5832871 * 2
def baseEnd_5832871 : Nat := 2995066418671353599087621

theorem tailTrace_5832871 : CollatzResearch.WordTrace tailWord_5832871 prefixEnd_5832871 2995066418671353599087621 := by
  unfold tailWord_5832871
  simp only [CollatzResearch.WordTrace]
  refine ⟨212742282851512016902362467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141828188567674677934908311 212742282851512016902362467)
  ·
    refine ⟨319113424277268025353543701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212742282851512016902362467 319113424277268025353543701)
    ·
      refine ⟨14958441762996938688447361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 319113424277268025353543701 14958441762996938688447361)
      ·
        refine ⟨11218831322247704016335521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14958441762996938688447361 11218831322247704016335521)
        ·
          refine ⟨8414123491685778012251641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11218831322247704016335521 8414123491685778012251641)
          ·
            refine ⟨6310592618764333509188731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8414123491685778012251641 6310592618764333509188731)
            ·
              refine ⟨9465888928146500263783097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310592618764333509188731 9465888928146500263783097)
              ·
                refine ⟨7099416696109875197837323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9465888928146500263783097 7099416696109875197837323)
                ·
                  refine ⟨10649125044164812796755985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099416696109875197837323 10649125044164812796755985)
                  ·
                    refine ⟨7986843783123609597566989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10649125044164812796755985 7986843783123609597566989)
                    ·
                      refine ⟨2995066418671353599087621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986843783123609597566989 2995066418671353599087621)
                      ·
                        rfl

theorem cell23_5832871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5832871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832871 prefixEnd_5832871 := by exact prefixLift 5832871
  have htrace : WordTrace (prefixWord ++ tailWord_5832871) baseStart_5832871 baseEnd_5832871 := by
    simpa [prefixWord, tailWord_5832871, baseEnd_5832871] using wordTrace_append hprefix tailTrace_5832871
  have hstable : (prefixWord ++ tailWord_5832871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832871).length < 2 ^ (prefixWord ++ tailWord_5832871).sum := by decide
  have hdescent : baseEnd_5832871 < baseStart_5832871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832883 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 4, 6]
def baseStart_5832883 : Nat := 118140960795 + 5832883 * 2 ^ 59
def prefixEnd_5832883 : Nat := 4983230072969 + 3 ^ 40 * 5832883 * 2
def baseEnd_5832883 : Nat := 998357526813069184045855

theorem tailTrace_5832883 : CollatzResearch.WordTrace tailWord_5832883 prefixEnd_5832883 998357526813069184045855 := by
  unfold tailWord_5832883
  simp only [CollatzResearch.WordTrace]
  refine ⟨212742720527468542951799303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141828480351645695301199535 212742720527468542951799303)
  ·
    refine ⟨319114080791202814427698955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212742720527468542951799303 319114080791202814427698955)
    ·
      refine ⟨478671121186804221641548433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319114080791202814427698955 478671121186804221641548433)
      ·
        refine ⟨359003340890103166231161325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478671121186804221641548433 359003340890103166231161325)
        ·
          refine ⟨134626252833788687336685497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359003340890103166231161325 134626252833788687336685497)
          ·
            refine ⟨100969689625341515502514123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134626252833788687336685497 100969689625341515502514123)
            ·
              refine ⟨151454534438012273253771185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100969689625341515502514123 151454534438012273253771185)
              ·
                refine ⟨113590900828509204940328389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151454534438012273253771185 113590900828509204940328389)
                ·
                  refine ⟨21298293905345475926311573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113590900828509204940328389 21298293905345475926311573)
                  ·
                    refine ⟨998357526813069184045855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21298293905345475926311573 998357526813069184045855)
                    ·
                      rfl

theorem cell23_5832883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_5832883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832883 prefixEnd_5832883 := by exact prefixLift 5832883
  have htrace : WordTrace (prefixWord ++ tailWord_5832883) baseStart_5832883 baseEnd_5832883 := by
    simpa [prefixWord, tailWord_5832883, baseEnd_5832883] using wordTrace_append hprefix tailTrace_5832883
  have hstable : (prefixWord ++ tailWord_5832883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832883).length < 2 ^ (prefixWord ++ tailWord_5832883).sum := by decide
  have hdescent : baseEnd_5832883 < baseStart_5832883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832903 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_5832903 : Nat := 118140960795 + 5832903 * 2 ^ 59
def prefixEnd_5832903 : Nat := 4983230072969 + 3 ^ 40 * 5832903 * 2
def baseEnd_5832903 : Nat := 2995082850052297473887473

theorem tailTrace_5832903 : CollatzResearch.WordTrace tailWord_5832903 prefixEnd_5832903 2995082850052297473887473 := by
  unfold tailWord_5832903
  simp only [CollatzResearch.WordTrace]
  refine ⟨212743449987396086367527363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141828966658264057578351575 212743449987396086367527363)
  ·
    refine ⟨319115174981094129551291045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212743449987396086367527363 319115174981094129551291045)
    ·
      refine ⟨59834095308955149290867071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319115174981094129551291045 59834095308955149290867071)
      ·
        refine ⟨89751142963432723936300607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59834095308955149290867071 89751142963432723936300607)
        ·
          refine ⟨134626714445149085904450911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89751142963432723936300607 134626714445149085904450911)
          ·
            refine ⟨201940071667723628856676367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134626714445149085904450911 201940071667723628856676367)
            ·
              refine ⟨302910107501585443285014551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201940071667723628856676367 302910107501585443285014551)
              ·
                refine ⟨454365161252378164927521827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302910107501585443285014551 454365161252378164927521827)
                ·
                  refine ⟨681547741878567247391282741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454365161252378164927521827 681547741878567247391282741)
                  ·
                    refine ⟨63895100801115679442932757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 681547741878567247391282741 63895100801115679442932757)
                    ·
                      refine ⟨2995082850052297473887473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63895100801115679442932757 2995082850052297473887473)
                      ·
                        rfl

theorem cell23_5832903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_5832903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832903 prefixEnd_5832903 := by exact prefixLift 5832903
  have htrace : WordTrace (prefixWord ++ tailWord_5832903) baseStart_5832903 baseEnd_5832903 := by
    simpa [prefixWord, tailWord_5832903, baseEnd_5832903] using wordTrace_append hprefix tailTrace_5832903
  have hstable : (prefixWord ++ tailWord_5832903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832903).length < 2 ^ (prefixWord ++ tailWord_5832903).sum := by decide
  have hdescent : baseEnd_5832903 < baseStart_5832903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832917 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_5832917 : Nat := 118140960795 + 5832917 * 2 ^ 59
def prefixEnd_5832917 : Nat := 4983230072969 + 3 ^ 40 * 5832917 * 2
def baseEnd_5832917 : Nat := 998363346260486806370803

theorem tailTrace_5832917 : CollatzResearch.WordTrace tailWord_5832917 prefixEnd_5832917 998363346260486806370803 := by
  unfold tailWord_5832917
  simp only [CollatzResearch.WordTrace]
  refine ⟨212743960609345366758537005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141829307072896911172358003 212743960609345366758537005)
  ·
    refine ⟨79778985228504512534451377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212743960609345366758537005 79778985228504512534451377)
    ·
      refine ⟨59834238921378384400838533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79778985228504512534451377 59834238921378384400838533)
      ·
        refine ⟨11218919797758447075157225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59834238921378384400838533 11218919797758447075157225)
        ·
          refine ⟨8414189848318835306367919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11218919797758447075157225 8414189848318835306367919)
          ·
            refine ⟨12621284772478252959551879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414189848318835306367919 12621284772478252959551879)
            ·
              refine ⟨18931927158717379439327819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621284772478252959551879 18931927158717379439327819)
              ·
                refine ⟨28397890738076069158991729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18931927158717379439327819 28397890738076069158991729)
                ·
                  refine ⟨21298418053557051869243797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28397890738076069158991729 21298418053557051869243797)
                  ·
                    refine ⟨998363346260486806370803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21298418053557051869243797 998363346260486806370803)
                    ·
                      rfl

theorem cell23_5832917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_5832917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832917 prefixEnd_5832917 := by exact prefixLift 5832917
  have htrace : WordTrace (prefixWord ++ tailWord_5832917) baseStart_5832917 baseEnd_5832917 := by
    simpa [prefixWord, tailWord_5832917, baseEnd_5832917] using wordTrace_append hprefix tailTrace_5832917
  have hstable : (prefixWord ++ tailWord_5832917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832917).length < 2 ^ (prefixWord ++ tailWord_5832917).sum := by decide
  have hdescent : baseEnd_5832917 < baseStart_5832917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832920 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_5832920 : Nat := 118140960795 + 5832920 * 2 ^ 59
def prefixEnd_5832920 : Nat := 4983230072969 + 3 ^ 40 * 5832920 * 2
def baseEnd_5832920 : Nat := 2995091579223423907374895

theorem tailTrace_5832920 : CollatzResearch.WordTrace tailWord_5832920 prefixEnd_5832920 2995091579223423907374895 := by
  unfold tailWord_5832920
  simp only [CollatzResearch.WordTrace]
  refine ⟨106372035014167249135448107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141829380018889665513930809 106372035014167249135448107)
  ·
    refine ⟨159558052521250873703172161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106372035014167249135448107 159558052521250873703172161)
    ·
      refine ⟨119668539390938155277379121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159558052521250873703172161 119668539390938155277379121)
      ·
        refine ⟨89751404543203616458034341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119668539390938155277379121 89751404543203616458034341)
        ·
          refine ⟨16828388351850678085881439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89751404543203616458034341 16828388351850678085881439)
          ·
            refine ⟨25242582527776017128822159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16828388351850678085881439 25242582527776017128822159)
            ·
              refine ⟨37863873791664025693233239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25242582527776017128822159 37863873791664025693233239)
              ·
                refine ⟨56795810687496038539849859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37863873791664025693233239 56795810687496038539849859)
                ·
                  refine ⟨85193716031244057809774789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56795810687496038539849859 85193716031244057809774789)
                  ·
                    refine ⟨15973821755858260839332773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85193716031244057809774789 15973821755858260839332773)
                    ·
                      refine ⟨2995091579223423907374895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15973821755858260839332773 2995091579223423907374895)
                      ·
                        rfl

theorem cell23_5832920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_5832920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832920 prefixEnd_5832920 := by exact prefixLift 5832920
  have htrace : WordTrace (prefixWord ++ tailWord_5832920) baseStart_5832920 baseEnd_5832920 := by
    simpa [prefixWord, tailWord_5832920, baseEnd_5832920] using wordTrace_append hprefix tailTrace_5832920
  have hstable : (prefixWord ++ tailWord_5832920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832920).length < 2 ^ (prefixWord ++ tailWord_5832920).sum := by decide
  have hdescent : baseEnd_5832920 < baseStart_5832920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832940 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_5832940 : Nat := 118140960795 + 5832940 * 2 ^ 59
def prefixEnd_5832940 : Nat := 4983230072969 + 3 ^ 40 * 5832940 * 2
def baseEnd_5832940 : Nat := 2995101848836513829124803

theorem tailTrace_5832940 : CollatzResearch.WordTrace tailWord_5832940 prefixEnd_5832940 2995101848836513829124803 := by
  unfold tailWord_5832940
  simp only [CollatzResearch.WordTrace]
  refine ⟨106372399744131020843312137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141829866325508027791082849 106372399744131020843312137)
  ·
    refine ⟨79779299808098265632484103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106372399744131020843312137 79779299808098265632484103)
    ·
      refine ⟨119668949712147398448726155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79779299808098265632484103 119668949712147398448726155)
      ·
        refine ⟨179503424568221097673089233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119668949712147398448726155 179503424568221097673089233)
        ·
          refine ⟨134627568426165823254816925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179503424568221097673089233 134627568426165823254816925)
          ·
            refine ⟨50485338159812183720556347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134627568426165823254816925 50485338159812183720556347)
            ·
              refine ⟨75728007239718275580834521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50485338159812183720556347 75728007239718275580834521)
              ·
                refine ⟨56796005429788706685625891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75728007239718275580834521 56796005429788706685625891)
                ·
                  refine ⟨85194008144683060028438837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56796005429788706685625891 85194008144683060028438837)
                  ·
                    refine ⟨7986938263564036877666141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85194008144683060028438837 7986938263564036877666141)
                    ·
                      refine ⟨2995101848836513829124803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7986938263564036877666141 2995101848836513829124803)
                      ·
                        rfl

theorem cell23_5832940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_5832940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832940 prefixEnd_5832940 := by exact prefixLift 5832940
  have htrace : WordTrace (prefixWord ++ tailWord_5832940) baseStart_5832940 baseEnd_5832940 := by
    simpa [prefixWord, tailWord_5832940, baseEnd_5832940] using wordTrace_append hprefix tailTrace_5832940
  have hstable : (prefixWord ++ tailWord_5832940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832940).length < 2 ^ (prefixWord ++ tailWord_5832940).sum := by decide
  have hdescent : baseEnd_5832940 < baseStart_5832940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832947 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 5]
def baseStart_5832947 : Nat := 118140960795 + 5832947 * 2 ^ 59
def prefixEnd_5832947 : Nat := 4983230072969 + 3 ^ 40 * 5832947 * 2
def baseEnd_5832947 : Nat := 332789493689010589081919

theorem tailTrace_5832947 : CollatzResearch.WordTrace tailWord_5832947 prefixEnd_5832947 332789493689010589081919 := by
  unfold tailWord_5832947
  simp only [CollatzResearch.WordTrace]
  refine ⟨212745054799236681882129095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141830036532824454588086063 212745054799236681882129095)
  ·
    refine ⟨319117582198855022823193643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212745054799236681882129095 319117582198855022823193643)
    ·
      refine ⟨478676373298282534234790465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319117582198855022823193643 478676373298282534234790465)
      ·
        refine ⟨359007279973711900676092849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478676373298282534234790465 359007279973711900676092849)
        ·
          refine ⟨269255459980283925507069637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359007279973711900676092849 269255459980283925507069637)
          ·
            refine ⟨50485398746303236032575557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269255459980283925507069637 50485398746303236032575557)
            ·
              refine ⟨9466012264931856756107917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50485398746303236032575557 9466012264931856756107917)
              ·
                refine ⟨3549754599349446283540469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9466012264931856756107917 3549754599349446283540469)
                ·
                  refine ⟨332789493689010589081919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549754599349446283540469 332789493689010589081919)
                  ·
                    rfl

theorem cell23_5832947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 5].length) (baseStart_5832947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832947 prefixEnd_5832947 := by exact prefixLift 5832947
  have htrace : WordTrace (prefixWord ++ tailWord_5832947) baseStart_5832947 baseEnd_5832947 := by
    simpa [prefixWord, tailWord_5832947, baseEnd_5832947] using wordTrace_append hprefix tailTrace_5832947
  have hstable : (prefixWord ++ tailWord_5832947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832947).length < 2 ^ (prefixWord ++ tailWord_5832947).sum := by decide
  have hdescent : baseEnd_5832947 < baseStart_5832947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832960 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_5832960 : Nat := 118140960795 + 5832960 * 2 ^ 59
def prefixEnd_5832960 : Nat := 4983230072969 + 3 ^ 40 * 5832960 * 2
def baseEnd_5832960 : Nat := 998370706149867916958237

theorem tailTrace_5832960 : CollatzResearch.WordTrace tailWord_5832960 prefixEnd_5832960 998370706149867916958237 := by
  unfold tailWord_5832960
  simp only [CollatzResearch.WordTrace]
  refine ⟨106372764474094792551176167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141830352632126390068234889 106372764474094792551176167)
  ·
    refine ⟨159559146711142188826764251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106372764474094792551176167 159559146711142188826764251)
    ·
      refine ⟨239338720066713283240146377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159559146711142188826764251 239338720066713283240146377)
      ·
        refine ⟨179504040050034962430109783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239338720066713283240146377 179504040050034962430109783)
        ·
          refine ⟨269256060075052443645164675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179504040050034962430109783 269256060075052443645164675)
          ·
            refine ⟨403884090112578665467747013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269256060075052443645164675 403884090112578665467747013)
            ·
              refine ⟨75728266896108499775202565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 403884090112578665467747013 75728266896108499775202565)
              ·
                refine ⟨14199050043020343707850481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75728266896108499775202565 14199050043020343707850481)
                ·
                  refine ⟨10649287532265257780887861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14199050043020343707850481 10649287532265257780887861)
                  ·
                    refine ⟨998370706149867916958237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10649287532265257780887861 998370706149867916958237)
                    ·
                      rfl

theorem cell23_5832960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_5832960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832960 prefixEnd_5832960 := by exact prefixLift 5832960
  have htrace : WordTrace (prefixWord ++ tailWord_5832960) baseStart_5832960 baseEnd_5832960 := by
    simpa [prefixWord, tailWord_5832960, baseEnd_5832960] using wordTrace_append hprefix tailTrace_5832960
  have hstable : (prefixWord ++ tailWord_5832960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832960).length < 2 ^ (prefixWord ++ tailWord_5832960).sum := by decide
  have hdescent : baseEnd_5832960 < baseStart_5832960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5832970 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5832970 : Nat := 118140960795 + 5832970 * 2 ^ 59
def prefixEnd_5832970 : Nat := 4983230072969 + 3 ^ 40 * 5832970 * 2
def baseEnd_5832970 : Nat := 2995117253256148711749665

theorem tailTrace_5832970 : CollatzResearch.WordTrace tailWord_5832970 prefixEnd_5832970 2995117253256148711749665 := by
  unfold tailWord_5832970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53186473419538339202554091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141830595785435571206810909 53186473419538339202554091)
  ·
    refine ⟨79779710129307508803831137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53186473419538339202554091 79779710129307508803831137)
    ·
      refine ⟨59834782596980631602873353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79779710129307508803831137 59834782596980631602873353)
      ·
        refine ⟨44876086947735473702155015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59834782596980631602873353 44876086947735473702155015)
        ·
          refine ⟨67314130421603210553232523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44876086947735473702155015 67314130421603210553232523)
          ·
            refine ⟨100971195632404815829848785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67314130421603210553232523 100971195632404815829848785)
            ·
              refine ⟨75728396724303611872386589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100971195632404815829848785 75728396724303611872386589)
              ·
                refine ⟨28398148771613854452144971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75728396724303611872386589 28398148771613854452144971)
                ·
                  refine ⟨42597223157420781678217457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28398148771613854452144971 42597223157420781678217457)
                  ·
                    refine ⟨31947917368065586258663093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42597223157420781678217457 31947917368065586258663093)
                    ·
                      refine ⟨2995117253256148711749665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31947917368065586258663093 2995117253256148711749665)
                      ·
                        rfl

theorem cell23_5832970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5832970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5832970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5832970 prefixEnd_5832970 := by exact prefixLift 5832970
  have htrace : WordTrace (prefixWord ++ tailWord_5832970) baseStart_5832970 baseEnd_5832970 := by
    simpa [prefixWord, tailWord_5832970, baseEnd_5832970] using wordTrace_append hprefix tailTrace_5832970
  have hstable : (prefixWord ++ tailWord_5832970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5832970).length < 2 ^ (prefixWord ++ tailWord_5832970).sum := by decide
  have hdescent : baseEnd_5832970 < baseStart_5832970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5832970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833020 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 8]
def baseStart_5833020 : Nat := 118140960795 + 5833020 * 2 ^ 59
def prefixEnd_5833020 : Nat := 4983230072969 + 3 ^ 40 * 5833020 * 2
def baseEnd_5833020 : Nat := 332793658587652612902715

theorem tailTrace_5833020 : CollatzResearch.WordTrace tailWord_5833020 prefixEnd_5833020 332793658587652612902715 := by
  unfold tailWord_5833020
  simp only [CollatzResearch.WordTrace]
  refine ⟨106373858663986107674768257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141831811551981476899691009 106373858663986107674768257)
  ·
    refine ⟨79780393997989580756076193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106373858663986107674768257 79780393997989580756076193)
    ·
      refine ⟨59835295498492185567057145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79780393997989580756076193 59835295498492185567057145)
      ·
        refine ⟨44876471623869139175292859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59835295498492185567057145 44876471623869139175292859)
        ·
          refine ⟨67314707435803708762939289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44876471623869139175292859 67314707435803708762939289)
          ·
            refine ⟨50486030576852781572204467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67314707435803708762939289 50486030576852781572204467)
            ·
              refine ⟨75729045865279172358306701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50486030576852781572204467 75729045865279172358306701)
              ·
                refine ⟨28398392199479689634365013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75729045865279172358306701 28398392199479689634365013)
                ·
                  refine ⟨332793658587652612902715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28398392199479689634365013 332793658587652612902715)
                  ·
                    rfl

theorem cell23_5833020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_5833020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833020 prefixEnd_5833020 := by exact prefixLift 5833020
  have htrace : WordTrace (prefixWord ++ tailWord_5833020) baseStart_5833020 baseEnd_5833020 := by
    simpa [prefixWord, tailWord_5833020, baseEnd_5833020] using wordTrace_append hprefix tailTrace_5833020
  have hstable : (prefixWord ++ tailWord_5833020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833020).length < 2 ^ (prefixWord ++ tailWord_5833020).sum := by decide
  have hdescent : baseEnd_5833020 < baseStart_5833020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833097 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_5833097 : Nat := 118140960795 + 5833097 * 2 ^ 59
def prefixEnd_5833097 : Nat := 4983230072969 + 3 ^ 40 * 5833097 * 2
def baseEnd_5833097 : Nat := 998394155099756571620527

theorem tailTrace_5833097 : CollatzResearch.WordTrace tailWord_5833097 prefixEnd_5833097 998394155099756571620527 := by
  unfold tailWord_5833097
  simp only [CollatzResearch.WordTrace]
  refine ⟨212750525748693257500089545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141833683832462171666726363 212750525748693257500089545)
  ·
    refine ⟨159562894311519943125067159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212750525748693257500089545 159562894311519943125067159)
    ·
      refine ⟨239344341467279914687600739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159562894311519943125067159 239344341467279914687600739)
      ·
        refine ⟨359016512200919872031401109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239344341467279914687600739 359016512200919872031401109)
        ·
          refine ⟨16828899009418119001471927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 359016512200919872031401109 16828899009418119001471927)
          ·
            refine ⟨25243348514127178502207891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16828899009418119001471927 25243348514127178502207891)
            ·
              refine ⟨37865022771190767753311837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25243348514127178502207891 37865022771190767753311837)
              ·
                refine ⟨14199383539196537907491939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37865022771190767753311837 14199383539196537907491939)
                ·
                  refine ⟨21299075308794806861237909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14199383539196537907491939 21299075308794806861237909)
                  ·
                    refine ⟨998394155099756571620527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21299075308794806861237909 998394155099756571620527)
                    ·
                      rfl

theorem cell23_5833097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_5833097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833097 prefixEnd_5833097 := by exact prefixLift 5833097
  have htrace : WordTrace (prefixWord ++ tailWord_5833097) baseStart_5833097 baseEnd_5833097 := by
    simpa [prefixWord, tailWord_5833097, baseEnd_5833097] using wordTrace_append hprefix tailTrace_5833097
  have hstable : (prefixWord ++ tailWord_5833097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833097).length < 2 ^ (prefixWord ++ tailWord_5833097).sum := by decide
  have hdescent : baseEnd_5833097 < baseStart_5833097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833098 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5833098 : Nat := 118140960795 + 5833098 * 2 ^ 59
def prefixEnd_5833098 : Nat := 4983230072969 + 3 ^ 40 * 5833098 * 2
def baseEnd_5833098 : Nat := 2995182978779924210949077

theorem tailTrace_5833098 : CollatzResearch.WordTrace tailWord_5833098 prefixEnd_5833098 2995182978779924210949077 := by
  unfold tailWord_5833098
  simp only [CollatzResearch.WordTrace]
  refine ⟨53187640555422408667718987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141833708147793089780583965 53187640555422408667718987)
  ·
    refine ⟨79781460833133613001578481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53187640555422408667718987 79781460833133613001578481)
    ·
      refine ⟨59836095624850209751183861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79781460833133613001578481 59836095624850209751183861)
      ·
        refine ⟨5609633964829707164173487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59836095624850209751183861 5609633964829707164173487)
        ·
          refine ⟨8414450947244560746260231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609633964829707164173487 8414450947244560746260231)
          ·
            refine ⟨12621676420866841119390347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414450947244560746260231 12621676420866841119390347)
            ·
              refine ⟨18932514631300261679085521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621676420866841119390347 18932514631300261679085521)
              ·
                refine ⟨14199385973475196259314141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18932514631300261679085521 14199385973475196259314141)
                ·
                  refine ⟨5324769740053198597242803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14199385973475196259314141 5324769740053198597242803)
                  ·
                    refine ⟨7987154610079797895864205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5324769740053198597242803 7987154610079797895864205)
                    ·
                      refine ⟨2995182978779924210949077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7987154610079797895864205 2995182978779924210949077)
                      ·
                        rfl

theorem cell23_5833098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5833098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833098 prefixEnd_5833098 := by exact prefixLift 5833098
  have htrace : WordTrace (prefixWord ++ tailWord_5833098) baseStart_5833098 baseEnd_5833098 := by
    simpa [prefixWord, tailWord_5833098, baseEnd_5833098] using wordTrace_append hprefix tailTrace_5833098
  have hstable : (prefixWord ++ tailWord_5833098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833098).length < 2 ^ (prefixWord ++ tailWord_5833098).sum := by decide
  have hdescent : baseEnd_5833098 < baseStart_5833098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833118 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_5833118 : Nat := 118140960795 + 5833118 * 2 ^ 59
def prefixEnd_5833118 : Nat := 4983230072969 + 3 ^ 40 * 5833118 * 2
def baseEnd_5833118 : Nat := 998397749464338044232995

theorem tailTrace_5833118 : CollatzResearch.WordTrace tailWord_5833118 prefixEnd_5833118 998397749464338044232995 := by
  unfold tailWord_5833118
  simp only [CollatzResearch.WordTrace]
  refine ⟨26593911460202147260825501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141834194454411452057736005 26593911460202147260825501)
  ·
    refine ⟨9972716797575805222809563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26593911460202147260825501 9972716797575805222809563)
    ·
      refine ⟨14959075196363707834214345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9972716797575805222809563 14959075196363707834214345)
      ·
        refine ⟨11219306397272780875660759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14959075196363707834214345 11219306397272780875660759)
        ·
          refine ⟨16828959595909171313491139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11219306397272780875660759 16828959595909171313491139)
          ·
            refine ⟨25243439393863756970236709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16828959595909171313491139 25243439393863756970236709)
            ·
              refine ⟨4733144886349454431919383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25243439393863756970236709 4733144886349454431919383)
              ·
                refine ⟨7099717329524181647879075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733144886349454431919383 7099717329524181647879075)
                ·
                  refine ⟨10649575994286272471818613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7099717329524181647879075 10649575994286272471818613)
                  ·
                    refine ⟨998397749464338044232995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10649575994286272471818613 998397749464338044232995)
                    ·
                      rfl

theorem cell23_5833118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_5833118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833118 prefixEnd_5833118 := by exact prefixLift 5833118
  have htrace : WordTrace (prefixWord ++ tailWord_5833118) baseStart_5833118 baseEnd_5833118 := by
    simpa [prefixWord, tailWord_5833118, baseEnd_5833118] using wordTrace_append hprefix tailTrace_5833118
  have hstable : (prefixWord ++ tailWord_5833118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833118).length < 2 ^ (prefixWord ++ tailWord_5833118).sum := by decide
  have hdescent : baseEnd_5833118 < baseStart_5833118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833127 : List Nat := [1, 1, 6, 1, 1, 3, 10]
def baseStart_5833127 : Nat := 118140960795 + 5833127 * 2 ^ 59
def prefixEnd_5833127 : Nat := 4983230072969 + 3 ^ 40 * 5833127 * 2
def baseEnd_5833127 : Nat := 36977751478011167870203

theorem tailTrace_5833127 : CollatzResearch.WordTrace tailWord_5833127 prefixEnd_5833127 36977751478011167870203 := by
  unfold tailWord_5833127
  simp only [CollatzResearch.WordTrace]
  refine ⟨212751619938584572623681635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141834413292389715082454423 212751619938584572623681635)
  ·
    refine ⟨319127429907876858935522453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212751619938584572623681635 319127429907876858935522453)
    ·
      refine ⟨14959098276931727762602615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 319127429907876858935522453 14959098276931727762602615)
      ·
        refine ⟨22438647415397591643903923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14959098276931727762602615 22438647415397591643903923)
        ·
          refine ⟨33657971123096387465855885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22438647415397591643903923 33657971123096387465855885)
          ·
            refine ⟨12621739171161145299695957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33657971123096387465855885 12621739171161145299695957)
            ·
              refine ⟨36977751478011167870203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12621739171161145299695957 36977751478011167870203)
              ·
                rfl

theorem cell23_5833127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 10].length) (baseStart_5833127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833127 prefixEnd_5833127 := by exact prefixLift 5833127
  have htrace : WordTrace (prefixWord ++ tailWord_5833127) baseStart_5833127 baseEnd_5833127 := by
    simpa [prefixWord, tailWord_5833127, baseEnd_5833127] using wordTrace_append hprefix tailTrace_5833127
  have hstable : (prefixWord ++ tailWord_5833127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833127).length < 2 ^ (prefixWord ++ tailWord_5833127).sum := by decide
  have hdescent : baseEnd_5833127 < baseStart_5833127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833138 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_5833138 : Nat := 118140960795 + 5833138 * 2 ^ 59
def prefixEnd_5833138 : Nat := 4983230072969 + 3 ^ 40 * 5833138 * 2
def baseEnd_5833138 : Nat := 2995203518006104054448893

theorem tailTrace_5833138 : CollatzResearch.WordTrace tailWord_5833138 prefixEnd_5833138 2995203518006104054448893 := by
  unfold tailWord_5833138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53188005285386180375583017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141834680761029814334888045 53188005285386180375583017)
  ·
    refine ⟨39891003964039635281687263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53188005285386180375583017 39891003964039635281687263)
    ·
      refine ⟨59836505946059452922530895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39891003964039635281687263 59836505946059452922530895)
      ·
        refine ⟨89754758919089179383796343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59836505946059452922530895 89754758919089179383796343)
        ·
          refine ⟨134632138378633769075694515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89754758919089179383796343 134632138378633769075694515)
          ·
            refine ⟨201948207567950653613541773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134632138378633769075694515 201948207567950653613541773)
            ·
              refine ⟨75730577837981495105078165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201948207567950653613541773 75730577837981495105078165)
              ·
                refine ⟨3549870836155382583050539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75730577837981495105078165 3549870836155382583050539)
                ·
                  refine ⟨5324806254233073874575809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549870836155382583050539 5324806254233073874575809)
                  ·
                    refine ⟨3993604690674805405931857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324806254233073874575809 3993604690674805405931857)
                    ·
                      refine ⟨2995203518006104054448893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993604690674805405931857 2995203518006104054448893)
                      ·
                        rfl

theorem cell23_5833138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_5833138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833138 prefixEnd_5833138 := by exact prefixLift 5833138
  have htrace : WordTrace (prefixWord ++ tailWord_5833138) baseStart_5833138 baseEnd_5833138 := by
    simpa [prefixWord, tailWord_5833138, baseEnd_5833138] using wordTrace_append hprefix tailTrace_5833138
  have hstable : (prefixWord ++ tailWord_5833138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833138).length < 2 ^ (prefixWord ++ tailWord_5833138).sum := by decide
  have hdescent : baseEnd_5833138 < baseStart_5833138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833148 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_5833148 : Nat := 118140960795 + 5833148 * 2 ^ 59
def prefixEnd_5833148 : Nat := 4983230072969 + 3 ^ 40 * 5833148 * 2
def baseEnd_5833148 : Nat := 998402884270883005107949

theorem tailTrace_5833148 : CollatzResearch.WordTrace tailWord_5833148 prefixEnd_5833148 998402884270883005107949 := by
  unfold tailWord_5833148
  simp only [CollatzResearch.WordTrace]
  refine ⟨106376192935754246605098049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141834923914338995473464065 106376192935754246605098049)
  ·
    refine ⟨79782144701815684953823537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106376192935754246605098049 79782144701815684953823537)
    ·
      refine ⟨59836608526361763715367653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79782144701815684953823537 59836608526361763715367653)
      ·
        refine ⟨11219364098692830696631435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59836608526361763715367653 11219364098692830696631435)
        ·
          refine ⟨16829046148039246044947153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11219364098692830696631435 16829046148039246044947153)
          ·
            refine ⟨12621784611029434533710365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16829046148039246044947153 12621784611029434533710365)
            ·
              refine ⟨4733169229136037950141387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12621784611029434533710365 4733169229136037950141387)
              ·
                refine ⟨7099753843704056925212081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733169229136037950141387 7099753843704056925212081)
                ·
                  refine ⟨5324815382778042693909061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099753843704056925212081 5324815382778042693909061)
                  ·
                    refine ⟨998402884270883005107949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324815382778042693909061 998402884270883005107949)
                    ·
                      rfl

theorem cell23_5833148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_5833148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833148 prefixEnd_5833148 := by exact prefixLift 5833148
  have htrace : WordTrace (prefixWord ++ tailWord_5833148) baseStart_5833148 baseEnd_5833148 := by
    simpa [prefixWord, tailWord_5833148, baseEnd_5833148] using wordTrace_append hprefix tailTrace_5833148
  have hstable : (prefixWord ++ tailWord_5833148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833148).length < 2 ^ (prefixWord ++ tailWord_5833148).sum := by decide
  have hdescent : baseEnd_5833148 < baseStart_5833148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833172 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_5833172 : Nat := 118140960795 + 5833172 * 2 ^ 59
def prefixEnd_5833172 : Nat := 4983230072969 + 3 ^ 40 * 5833172 * 2
def baseEnd_5833172 : Nat := 2995220976348356921423737

theorem tailTrace_5833172 : CollatzResearch.WordTrace tailWord_5833172 prefixEnd_5833172 2995220976348356921423737 := by
  unfold tailWord_5833172
  simp only [CollatzResearch.WordTrace]
  refine ⟨106376630611710772654534885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141835507482281030206046513 106376630611710772654534885)
  ·
    refine ⟨19945618239695769872725291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106376630611710772654534885 19945618239695769872725291)
    ·
      refine ⟨29918427359543654809087937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19945618239695769872725291 29918427359543654809087937)
      ·
        refine ⟨22438820519657741106815953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29918427359543654809087937 22438820519657741106815953)
        ·
          refine ⟨16829115389743305830111965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22438820519657741106815953 16829115389743305830111965)
          ·
            refine ⟨6310918271153739686291987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16829115389743305830111965 6310918271153739686291987)
            ·
              refine ⟨9466377406730609529437981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310918271153739686291987 9466377406730609529437981)
              ·
                refine ⟨3549891527523978573539243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9466377406730609529437981 3549891527523978573539243)
                ·
                  refine ⟨5324837291285967860308865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549891527523978573539243 5324837291285967860308865)
                  ·
                    refine ⟨3993627968464475895231649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324837291285967860308865 3993627968464475895231649)
                    ·
                      refine ⟨2995220976348356921423737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993627968464475895231649 2995220976348356921423737)
                      ·
                        rfl

theorem cell23_5833172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_5833172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833172 prefixEnd_5833172 := by exact prefixLift 5833172
  have htrace : WordTrace (prefixWord ++ tailWord_5833172) baseStart_5833172 baseEnd_5833172 := by
    simpa [prefixWord, tailWord_5833172, baseEnd_5833172] using wordTrace_append hprefix tailTrace_5833172
  have hstable : (prefixWord ++ tailWord_5833172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833172).length < 2 ^ (prefixWord ++ tailWord_5833172).sum := by decide
  have hdescent : baseEnd_5833172 < baseStart_5833172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833205 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5833205 : Nat := 118140960795 + 5833205 * 2 ^ 59
def prefixEnd_5833205 : Nat := 4983230072969 + 3 ^ 40 * 5833205 * 2
def baseEnd_5833205 : Nat := 2995237921209955292311085

theorem tailTrace_5833205 : CollatzResearch.WordTrace tailWord_5833205 prefixEnd_5833205 2995237921209955292311085 := by
  unfold tailWord_5833205
  simp only [CollatzResearch.WordTrace]
  refine ⟨212754464832301991945021069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141836309888201327963347379 212754464832301991945021069)
  ·
    refine ⟨79782924312113246979382901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212754464832301991945021069 79782924312113246979382901)
    ·
      refine ⟨7479649154260616904317147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79782924312113246979382901 7479649154260616904317147)
      ·
        refine ⟨11219473731390925356475721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7479649154260616904317147 11219473731390925356475721)
        ·
          refine ⟨8414605298543194017356791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11219473731390925356475721 8414605298543194017356791)
          ·
            refine ⟨12621907947814791026035187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414605298543194017356791 12621907947814791026035187)
            ·
              refine ⟨18932861921722186539052781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621907947814791026035187 18932861921722186539052781)
              ·
                refine ⟨7099823220645819952144793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18932861921722186539052781 7099823220645819952144793)
                ·
                  refine ⟨5324867415484364964108595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099823220645819952144793 5324867415484364964108595)
                  ·
                    refine ⟨7987301123226547446162893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5324867415484364964108595 7987301123226547446162893)
                    ·
                      refine ⟨2995237921209955292311085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7987301123226547446162893 2995237921209955292311085)
                      ·
                        rfl

theorem cell23_5833205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5833205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833205 prefixEnd_5833205 := by exact prefixLift 5833205
  have htrace : WordTrace (prefixWord ++ tailWord_5833205) baseStart_5833205 baseEnd_5833205 := by
    simpa [prefixWord, tailWord_5833205, baseEnd_5833205] using wordTrace_append hprefix tailTrace_5833205
  have hstable : (prefixWord ++ tailWord_5833205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833205).length < 2 ^ (prefixWord ++ tailWord_5833205).sum := by decide
  have hdescent : baseEnd_5833205 < baseStart_5833205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833207 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_5833207 : Nat := 118140960795 + 5833207 * 2 ^ 59
def prefixEnd_5833207 : Nat := 4983230072969 + 3 ^ 40 * 5833207 * 2
def baseEnd_5833207 : Nat := 2995238948171264284486075

theorem tailTrace_5833207 : CollatzResearch.WordTrace tailWord_5833207 prefixEnd_5833207 2995238948171264284486075 := by
  unfold tailWord_5833207
  simp only [CollatzResearch.WordTrace]
  refine ⟨212754537778294746286593875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141836358518863164191062583 212754537778294746286593875)
  ·
    refine ⟨319131806667442119429890813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212754537778294746286593875 319131806667442119429890813)
    ·
      refine ⟨119674427500290794786209055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319131806667442119429890813 119674427500290794786209055)
      ·
        refine ⟨179511641250436192179313583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119674427500290794786209055 179511641250436192179313583)
        ·
          refine ⟨269267461875654288268970375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179511641250436192179313583 269267461875654288268970375)
          ·
            refine ⟨403901192813481432403455563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269267461875654288268970375 403901192813481432403455563)
            ·
              refine ⟨605851789220222148605183345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403901192813481432403455563 605851789220222148605183345)
              ·
                refine ⟨454388841915166611453887509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605851789220222148605183345 454388841915166611453887509)
                ·
                  refine ⟨21299476964773434911900977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 454388841915166611453887509 21299476964773434911900977)
                  ·
                    refine ⟨15974607723580076183925733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21299476964773434911900977 15974607723580076183925733)
                    ·
                      refine ⟨2995238948171264284486075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15974607723580076183925733 2995238948171264284486075)
                      ·
                        rfl

theorem cell23_5833207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_5833207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833207 prefixEnd_5833207 := by exact prefixLift 5833207
  have htrace : WordTrace (prefixWord ++ tailWord_5833207) baseStart_5833207 baseEnd_5833207 := by
    simpa [prefixWord, tailWord_5833207, baseEnd_5833207] using wordTrace_append hprefix tailTrace_5833207
  have hstable : (prefixWord ++ tailWord_5833207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833207).length < 2 ^ (prefixWord ++ tailWord_5833207).sum := by decide
  have hdescent : baseEnd_5833207 < baseStart_5833207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833245 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_5833245 : Nat := 118140960795 + 5833245 * 2 ^ 59
def prefixEnd_5833245 : Nat := 4983230072969 + 3 ^ 40 * 5833245 * 2
def baseEnd_5833245 : Nat := 2995258460436135135810901

theorem tailTrace_5833245 : CollatzResearch.WordTrace tailWord_5833245 prefixEnd_5833245 2995258460436135135810901 := by
  unfold tailWord_5833245
  simp only [CollatzResearch.WordTrace]
  refine ⟨212755923752157078776477189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141837282501438052517651459 212755923752157078776477189)
  ·
    refine ⟨39891735703529452270589473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212755923752157078776477189 39891735703529452270589473)
    ·
      refine ⟨29918801777647089202942105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39891735703529452270589473 29918801777647089202942105)
      ·
        refine ⟨22439101333235316902206579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29918801777647089202942105 22439101333235316902206579)
        ·
          refine ⟨33658651999852975353309869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22439101333235316902206579 33658651999852975353309869)
          ·
            refine ⟨12621994499944865757491201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33658651999852975353309869 12621994499944865757491201)
            ·
              refine ⟨9466495874958649318118401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12621994499944865757491201 9466495874958649318118401)
              ·
                refine ⟨7099871906218986988588801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9466495874958649318118401 7099871906218986988588801)
                ·
                  refine ⟨5324903929664240241441601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099871906218986988588801 5324903929664240241441601)
                  ·
                    refine ⟨3993677947248180181081201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324903929664240241441601 3993677947248180181081201)
                    ·
                      refine ⟨2995258460436135135810901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993677947248180181081201 2995258460436135135810901)
                      ·
                        rfl

theorem cell23_5833245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_5833245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833245 prefixEnd_5833245 := by exact prefixLift 5833245
  have htrace : WordTrace (prefixWord ++ tailWord_5833245) baseStart_5833245 baseEnd_5833245 := by
    simpa [prefixWord, tailWord_5833245, baseEnd_5833245] using wordTrace_append hprefix tailTrace_5833245
  have hstable : (prefixWord ++ tailWord_5833245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833245).length < 2 ^ (prefixWord ++ tailWord_5833245).sum := by decide
  have hdescent : baseEnd_5833245 < baseStart_5833245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833247 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 7]
def baseStart_5833247 : Nat := 118140960795 + 5833247 * 2 ^ 59
def prefixEnd_5833247 : Nat := 4983230072969 + 3 ^ 40 * 5833247 * 2
def baseEnd_5833247 : Nat := 998419829132481375995297

theorem tailTrace_5833247 : CollatzResearch.WordTrace tailWord_5833247 prefixEnd_5833247 998419829132481375995297 := by
  unfold tailWord_5833247
  simp only [CollatzResearch.WordTrace]
  refine ⟨212755996698149833118049995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141837331132099888745366663 212755996698149833118049995)
  ·
    refine ⟨319133995047224749677074993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212755996698149833118049995 319133995047224749677074993)
    ·
      refine ⟨239350496285418562257806245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319133995047224749677074993 239350496285418562257806245)
      ·
        refine ⟨44878218053515980423338671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239350496285418562257806245 44878218053515980423338671)
        ·
          refine ⟨67317327080273970635008007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44878218053515980423338671 67317327080273970635008007)
          ·
            refine ⟨100975990620410955952512011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67317327080273970635008007 100975990620410955952512011)
            ·
              refine ⟨151463985930616433928768017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100975990620410955952512011 151463985930616433928768017)
              ·
                refine ⟨113597989447962325446576013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151463985930616433928768017 113597989447962325446576013)
                ·
                  refine ⟨42599246042985872042466005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113597989447962325446576013 42599246042985872042466005)
                  ·
                    refine ⟨998419829132481375995297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42599246042985872042466005 998419829132481375995297)
                    ·
                      rfl

theorem cell23_5833247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_5833247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833247 prefixEnd_5833247 := by exact prefixLift 5833247
  have htrace : WordTrace (prefixWord ++ tailWord_5833247) baseStart_5833247 baseEnd_5833247 := by
    simpa [prefixWord, tailWord_5833247, baseEnd_5833247] using wordTrace_append hprefix tailTrace_5833247
  have hstable : (prefixWord ++ tailWord_5833247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833247).length < 2 ^ (prefixWord ++ tailWord_5833247).sum := by decide
  have hdescent : baseEnd_5833247 < baseStart_5833247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833251 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 5]
def baseStart_5833251 : Nat := 118140960795 + 5833251 * 2 ^ 59
def prefixEnd_5833251 : Nat := 4983230072969 + 3 ^ 40 * 5833251 * 2
def baseEnd_5833251 : Nat := 332806837924451345815097

theorem tailTrace_5833251 : CollatzResearch.WordTrace tailWord_5833251 prefixEnd_5833251 332806837924451345815097 := by
  unfold tailWord_5833251
  simp only [CollatzResearch.WordTrace]
  refine ⟨212756142590135341801195607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141837428393423561200797071 212756142590135341801195607)
  ·
    refine ⟨319134213885203012701793411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212756142590135341801195607 319134213885203012701793411)
    ·
      refine ⟨478701320827804519052690117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319134213885203012701793411 478701320827804519052690117)
      ·
        refine ⟨89756497655213347322379397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 478701320827804519052690117 89756497655213347322379397)
        ·
          refine ⟨16829343310352502622946137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89756497655213347322379397 16829343310352502622946137)
          ·
            refine ⟨12622007482764376967209603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16829343310352502622946137 12622007482764376967209603)
            ·
              refine ⟨18933011224146565450814405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622007482764376967209603 18933011224146565450814405)
              ·
                refine ⟨3549939604527481022027701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18933011224146565450814405 3549939604527481022027701)
                ·
                  refine ⟨332806837924451345815097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549939604527481022027701 332806837924451345815097)
                  ·
                    rfl

theorem cell23_5833251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 5].length) (baseStart_5833251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833251 prefixEnd_5833251 := by exact prefixLift 5833251
  have htrace : WordTrace (prefixWord ++ tailWord_5833251) baseStart_5833251 baseEnd_5833251 := by
    simpa [prefixWord, tailWord_5833251, baseEnd_5833251] using wordTrace_append hprefix tailTrace_5833251
  have hstable : (prefixWord ++ tailWord_5833251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833251).length < 2 ^ (prefixWord ++ tailWord_5833251).sum := by decide
  have hdescent : baseEnd_5833251 < baseStart_5833251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833268 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 7]
def baseStart_5833268 : Nat := 118140960795 + 5833268 * 2 ^ 59
def prefixEnd_5833268 : Nat := 4983230072969 + 3 ^ 40 * 5833268 * 2
def baseEnd_5833268 : Nat := 332807807832354282869255

theorem tailTrace_5833268 : CollatzResearch.WordTrace tailWord_5833268 prefixEnd_5833268 332807807832354282869255 := by
  unfold tailWord_5833268
  simp only [CollatzResearch.WordTrace]
  refine ⟨106378381315536876852282229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141837841754049169136376305 106378381315536876852282229)
  ·
    refine ⟨9972973248331582204901459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106378381315536876852282229 9972973248331582204901459)
    ·
      refine ⟨14959459872497373307352189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9972973248331582204901459 14959459872497373307352189)
      ·
        refine ⟨5609797452186514990257071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14959459872497373307352189 5609797452186514990257071)
        ·
          refine ⟨8414696178279772485385607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609797452186514990257071 8414696178279772485385607)
          ·
            refine ⟨12622044267419658728078411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414696178279772485385607 12622044267419658728078411)
            ·
              refine ⟨18933066401129488092117617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622044267419658728078411 18933066401129488092117617)
              ·
                refine ⟨14199799800847116069088213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18933066401129488092117617 14199799800847116069088213)
                ·
                  refine ⟨332807807832354282869255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14199799800847116069088213 332807807832354282869255)
                  ·
                    rfl

theorem cell23_5833268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_5833268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833268 prefixEnd_5833268 := by exact prefixLift 5833268
  have htrace : WordTrace (prefixWord ++ tailWord_5833268) baseStart_5833268 baseEnd_5833268 := by
    simpa [prefixWord, tailWord_5833268, baseEnd_5833268] using wordTrace_append hprefix tailTrace_5833268
  have hstable : (prefixWord ++ tailWord_5833268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833268).length < 2 ^ (prefixWord ++ tailWord_5833268).sum := by decide
  have hdescent : baseEnd_5833268 < baseStart_5833268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833281 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5833281 : Nat := 118140960795 + 5833281 * 2 ^ 59
def prefixEnd_5833281 : Nat := 4983230072969 + 3 ^ 40 * 5833281 * 2
def baseEnd_5833281 : Nat := 998425648579898998320245

theorem tailTrace_5833281 : CollatzResearch.WordTrace tailWord_5833281 prefixEnd_5833281 998425648579898998320245 := by
  unfold tailWord_5833281
  simp only [CollatzResearch.WordTrace]
  refine ⟨212757236780026656924787697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141838157853351104616525131 212757236780026656924787697)
  ·
    refine ⟨159567927585019992693590773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212757236780026656924787697 159567927585019992693590773)
    ·
      refine ⟨14959493211095624315024135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159567927585019992693590773 14959493211095624315024135)
      ·
        refine ⟨22439239816643436472536203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14959493211095624315024135 22439239816643436472536203)
        ·
          refine ⟨33658859724965154708804305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22439239816643436472536203 33658859724965154708804305)
          ·
            refine ⟨25244144793723866031603229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33658859724965154708804305 25244144793723866031603229)
            ·
              refine ⟨9466554297646449761851211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25244144793723866031603229 9466554297646449761851211)
              ·
                refine ⟨14199831446469674642776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9466554297646449761851211 14199831446469674642776817)
                ·
                  refine ⟨10649873584852255982082613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14199831446469674642776817 10649873584852255982082613)
                  ·
                    refine ⟨998425648579898998320245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10649873584852255982082613 998425648579898998320245)
                    ·
                      rfl

theorem cell23_5833281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5833281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833281 prefixEnd_5833281 := by exact prefixLift 5833281
  have htrace : WordTrace (prefixWord ++ tailWord_5833281) baseStart_5833281 baseEnd_5833281 := by
    simpa [prefixWord, tailWord_5833281, baseEnd_5833281] using wordTrace_append hprefix tailTrace_5833281
  have hstable : (prefixWord ++ tailWord_5833281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833281).length < 2 ^ (prefixWord ++ tailWord_5833281).sum := by decide
  have hdescent : baseEnd_5833281 < baseStart_5833281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833301 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5833301 : Nat := 118140960795 + 5833301 * 2 ^ 59
def prefixEnd_5833301 : Nat := 4983230072969 + 3 ^ 40 * 5833301 * 2
def baseEnd_5833301 : Nat := 2995287215352786916710643

theorem tailTrace_5833301 : CollatzResearch.WordTrace tailWord_5833301 prefixEnd_5833301 2995287215352786916710643 := by
  unfold tailWord_5833301
  simp only [CollatzResearch.WordTrace]
  refine ⟨212757966239954200340515757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141838644159969466893677171 212757966239954200340515757)
  ·
    refine ⟨79784237339982825127693409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212757966239954200340515757 79784237339982825127693409)
    ·
      refine ⟨59838178004987118845770057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79784237339982825127693409 59838178004987118845770057)
      ·
        refine ⟨44878633503740339134327543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59838178004987118845770057 44878633503740339134327543)
        ·
          refine ⟨67317950255610508701491315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44878633503740339134327543 67317950255610508701491315)
          ·
            refine ⟨100976925383415763052236973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67317950255610508701491315 100976925383415763052236973)
            ·
              refine ⟨37866347018780911144588865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100976925383415763052236973 37866347018780911144588865)
              ·
                refine ⟨28399760264085683358441649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37866347018780911144588865 28399760264085683358441649)
                ·
                  refine ⟨21299820198064262518831237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28399760264085683358441649 21299820198064262518831237)
                  ·
                    refine ⟨3993716287137049222280857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21299820198064262518831237 3993716287137049222280857)
                    ·
                      refine ⟨2995287215352786916710643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993716287137049222280857 2995287215352786916710643)
                      ·
                        rfl

theorem cell23_5833301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5833301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833301 prefixEnd_5833301 := by exact prefixLift 5833301
  have htrace : WordTrace (prefixWord ++ tailWord_5833301) baseStart_5833301 baseEnd_5833301 := by
    simpa [prefixWord, tailWord_5833301, baseEnd_5833301] using wordTrace_append hprefix tailTrace_5833301
  have hstable : (prefixWord ++ tailWord_5833301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833301).length < 2 ^ (prefixWord ++ tailWord_5833301).sum := by decide
  have hdescent : baseEnd_5833301 < baseStart_5833301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833324 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 6]
def baseStart_5833324 : Nat := 118140960795 + 5833324 * 2 ^ 59
def prefixEnd_5833324 : Nat := 4983230072969 + 3 ^ 40 * 5833324 * 2
def baseEnd_5833324 : Nat := 332811002823093369635893

theorem tailTrace_5833324 : CollatzResearch.WordTrace tailWord_5833324 prefixEnd_5833324 332811002823093369635893 := by
  unfold tailWord_5833324
  simp only [CollatzResearch.WordTrace]
  refine ⟨106379402559435437634301513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141839203412580583512402017 106379402559435437634301513)
  ·
    refine ⟨79784551919576578225726135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106379402559435437634301513 79784551919576578225726135)
    ·
      refine ⟨119676827879364867338589203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79784551919576578225726135 119676827879364867338589203)
      ·
        refine ⟨179515241819047301007883805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119676827879364867338589203 179515241819047301007883805)
        ·
          refine ⟨67318215682142737877956427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179515241819047301007883805 67318215682142737877956427)
          ·
            refine ⟨100977323523214106816934641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67318215682142737877956427 100977323523214106816934641)
            ·
              refine ⟨75732992642410580112700981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100977323523214106816934641 75732992642410580112700981)
              ·
                refine ⟨7099968060225991885565717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75732992642410580112700981 7099968060225991885565717)
                ·
                  refine ⟨332811002823093369635893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7099968060225991885565717 332811002823093369635893)
                  ·
                    rfl

theorem cell23_5833324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_5833324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833324 prefixEnd_5833324 := by exact prefixLift 5833324
  have htrace : WordTrace (prefixWord ++ tailWord_5833324) baseStart_5833324 baseEnd_5833324 := by
    simpa [prefixWord, tailWord_5833324, baseEnd_5833324] using wordTrace_append hprefix tailTrace_5833324
  have hstable : (prefixWord ++ tailWord_5833324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833324).length < 2 ^ (prefixWord ++ tailWord_5833324).sum := by decide
  have hdescent : baseEnd_5833324 < baseStart_5833324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833362 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5833362 : Nat := 118140960795 + 5833362 * 2 ^ 59
def prefixEnd_5833362 : Nat := 4983230072969 + 3 ^ 40 * 5833362 * 2
def baseEnd_5833362 : Nat := 998439512557570392682621

theorem tailTrace_5833362 : CollatzResearch.WordTrace tailWord_5833362 prefixEnd_5833362 998439512557570392682621 := by
  unfold tailWord_5833362
  simp only [CollatzResearch.WordTrace]
  refine ⟨53190047773183301939621585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141840127395155471838990893 53190047773183301939621585)
  ·
    refine ⟨39892535829887476454716189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53190047773183301939621585 39892535829887476454716189)
    ·
      refine ⟨14959700936207803670518571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39892535829887476454716189 14959700936207803670518571)
      ·
        refine ⟨22439551404311705505777857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14959700936207803670518571 22439551404311705505777857)
        ·
          refine ⟨16829663553233779129333393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22439551404311705505777857 16829663553233779129333393)
          ·
            refine ⟨12622247664925334347000045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16829663553233779129333393 12622247664925334347000045)
            ·
              refine ⟨4733342874347000380125017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12622247664925334347000045 4733342874347000380125017)
              ·
                refine ⟨3550007155760250285093763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733342874347000380125017 3550007155760250285093763)
                ·
                  refine ⟨5325010733640375427640645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550007155760250285093763 5325010733640375427640645)
                  ·
                    refine ⟨998439512557570392682621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5325010733640375427640645 998439512557570392682621)
                    ·
                      rfl

theorem cell23_5833362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5833362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833362 prefixEnd_5833362 := by exact prefixLift 5833362
  have htrace : WordTrace (prefixWord ++ tailWord_5833362) baseStart_5833362 baseEnd_5833362 := by
    simpa [prefixWord, tailWord_5833362, baseEnd_5833362] using wordTrace_append hprefix tailTrace_5833362
  have hstable : (prefixWord ++ tailWord_5833362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833362).length < 2 ^ (prefixWord ++ tailWord_5833362).sum := by decide
  have hdescent : baseEnd_5833362 < baseStart_5833362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833391 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_5833391 : Nat := 118140960795 + 5833391 * 2 ^ 59
def prefixEnd_5833391 : Nat := 4983230072969 + 3 ^ 40 * 5833391 * 2
def baseEnd_5833391 : Nat := 2995333428611691564585229

theorem tailTrace_5833391 : CollatzResearch.WordTrace tailWord_5833391 prefixEnd_5833391 2995333428611691564585229 := by
  unfold tailWord_5833391
  simp only [CollatzResearch.WordTrace]
  refine ⟨212761248809628145711292027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141840832539752097140861351 212761248809628145711292027)
  ·
    refine ⟨319141873214442218566938041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212761248809628145711292027 319141873214442218566938041)
    ·
      refine ⟨239356404910831663925203531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319141873214442218566938041 239356404910831663925203531)
      ·
        refine ⟨359034607366247495887805297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239356404910831663925203531 359034607366247495887805297)
        ·
          refine ⟨269275955524685621915853973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359034607366247495887805297 269275955524685621915853973)
          ·
            refine ⟨12622310415219638527305655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269275955524685621915853973 12622310415219638527305655)
            ·
              refine ⟨18933465622829457790958483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622310415219638527305655 18933465622829457790958483)
              ·
                refine ⟨28400198434244186686437725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18933465622829457790958483 28400198434244186686437725)
                ·
                  refine ⟨10650074412841570007414147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28400198434244186686437725 10650074412841570007414147)
                  ·
                    refine ⟨15975111619262355011121221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10650074412841570007414147 15975111619262355011121221)
                    ·
                      refine ⟨2995333428611691564585229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15975111619262355011121221 2995333428611691564585229)
                      ·
                        rfl

theorem cell23_5833391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_5833391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833391 prefixEnd_5833391 := by exact prefixLift 5833391
  have htrace : WordTrace (prefixWord ++ tailWord_5833391) baseStart_5833391 baseEnd_5833391 := by
    simpa [prefixWord, tailWord_5833391, baseEnd_5833391] using wordTrace_append hprefix tailTrace_5833391
  have hstable : (prefixWord ++ tailWord_5833391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833391).length < 2 ^ (prefixWord ++ tailWord_5833391).sum := by decide
  have hdescent : baseEnd_5833391 < baseStart_5833391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833418 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_5833418 : Nat := 118140960795 + 5833418 * 2 ^ 59
def prefixEnd_5833418 : Nat := 4983230072969 + 3 ^ 40 * 5833418 * 2
def baseEnd_5833418 : Nat := 998449097529787652982535

theorem tailTrace_5833418 : CollatzResearch.WordTrace tailWord_5833418 prefixEnd_5833418 998449097529787652982535 := by
  unfold tailWord_5833418
  simp only [CollatzResearch.WordTrace]
  refine ⟨53190558395132582330631227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141841489053686886215016605 53190558395132582330631227)
  ·
    refine ⟨79785837592698873495946841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53190558395132582330631227 79785837592698873495946841)
    ·
      refine ⟨59839378194524155121960131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79785837592698873495946841 59839378194524155121960131)
      ·
        refine ⟨89759067291786232682940197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59839378194524155121960131 89759067291786232682940197)
        ·
          refine ⟨16829825117209918628051287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89759067291786232682940197 16829825117209918628051287)
          ·
            refine ⟨25244737675814877942076931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16829825117209918628051287 25244737675814877942076931)
            ·
              refine ⟨37867106513722316913115397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25244737675814877942076931 37867106513722316913115397)
              ·
                refine ⟨7100082471322934421209137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37867106513722316913115397 7100082471322934421209137)
                ·
                  refine ⟨5325061853492200815906853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7100082471322934421209137 5325061853492200815906853)
                  ·
                    refine ⟨998449097529787652982535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5325061853492200815906853 998449097529787652982535)
                    ·
                      rfl

theorem cell23_5833418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_5833418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833418 prefixEnd_5833418 := by exact prefixLift 5833418
  have htrace : WordTrace (prefixWord ++ tailWord_5833418) baseStart_5833418 baseEnd_5833418 := by
    simpa [prefixWord, tailWord_5833418, baseEnd_5833418] using wordTrace_append hprefix tailTrace_5833418
  have hstable : (prefixWord ++ tailWord_5833418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833418).length < 2 ^ (prefixWord ++ tailWord_5833418).sum := by decide
  have hdescent : baseEnd_5833418 < baseStart_5833418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833431 : List Nat := [1, 1, 3, 2, 1, 6, 1, 8]
def baseStart_5833431 : Nat := 118140960795 + 5833431 * 2 ^ 59
def prefixEnd_5833431 : Nat := 4983230072969 + 3 ^ 40 * 5833431 * 2
def baseEnd_5833431 : Nat := 110939035845847089188335

theorem tailTrace_5833431 : CollatzResearch.WordTrace tailWord_5833431 prefixEnd_5833431 110939035845847089188335 := by
  unfold tailWord_5833431
  simp only [CollatzResearch.WordTrace]
  refine ⟨212762707729483232542748147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141841805152988821695165431 212762707729483232542748147)
  ·
    refine ⟨319144061594224848814122221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212762707729483232542748147 319144061594224848814122221)
    ·
      refine ⟨119679023097834318305295833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319144061594224848814122221 119679023097834318305295833)
      ·
        refine ⟨89759267323375738728971875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119679023097834318305295833 89759267323375738728971875)
        ·
          refine ⟨134638900985063608093457813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89759267323375738728971875 134638900985063608093457813)
          ·
            refine ⟨6311198483674856629380835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134638900985063608093457813 6311198483674856629380835)
            ·
              refine ⟨9466797725512284944071253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311198483674856629380835 9466797725512284944071253)
              ·
                refine ⟨110939035845847089188335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9466797725512284944071253 110939035845847089188335)
                ·
                  rfl

theorem cell23_5833431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 8].length) (baseStart_5833431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833431 prefixEnd_5833431 := by exact prefixLift 5833431
  have htrace : WordTrace (prefixWord ++ tailWord_5833431) baseStart_5833431 baseEnd_5833431 := by
    simpa [prefixWord, tailWord_5833431, baseEnd_5833431] using wordTrace_append hprefix tailTrace_5833431
  have hstable : (prefixWord ++ tailWord_5833431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833431).length < 2 ^ (prefixWord ++ tailWord_5833431).sum := by decide
  have hdescent : baseEnd_5833431 < baseStart_5833431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833448 : List Nat := [2, 1, 4, 1, 4, 1, 3, 7]
def baseStart_5833448 : Nat := 118140960795 + 5833448 * 2 ^ 59
def prefixEnd_5833448 : Nat := 4983230072969 + 3 ^ 40 * 5833448 * 2
def baseEnd_5833448 : Nat := 110939359148481401539721

theorem tailTrace_5833448 : CollatzResearch.WordTrace tailWord_5833448 prefixEnd_5833448 110939359148481401539721 := by
  unfold tailWord_5833448
  simp only [CollatzResearch.WordTrace]
  refine ⟨106381663885210822223058499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141842218513614429630744665 106381663885210822223058499)
  ·
    refine ⟨159572495827816233334587749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106381663885210822223058499 159572495827816233334587749)
    ·
      refine ⟨29919842967715543750235203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159572495827816233334587749 29919842967715543750235203)
      ·
        refine ⟨44879764451573315625352805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29919842967715543750235203 44879764451573315625352805)
        ·
          refine ⟨8414955834669996679753651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44879764451573315625352805 8414955834669996679753651)
          ·
            refine ⟨12622433752004995019630477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414955834669996679753651 12622433752004995019630477)
            ·
              refine ⟨4733412657001873132361429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12622433752004995019630477 4733412657001873132361429)
              ·
                refine ⟨110939359148481401539721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4733412657001873132361429 110939359148481401539721)
                ·
                  rfl

theorem cell23_5833448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 7].length) (baseStart_5833448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833448 prefixEnd_5833448 := by exact prefixLift 5833448
  have htrace : WordTrace (prefixWord ++ tailWord_5833448) baseStart_5833448 baseEnd_5833448 := by
    simpa [prefixWord, tailWord_5833448, baseEnd_5833448] using wordTrace_append hprefix tailTrace_5833448
  have hstable : (prefixWord ++ tailWord_5833448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833448).length < 2 ^ (prefixWord ++ tailWord_5833448).sum := by decide
  have hdescent : baseEnd_5833448 < baseStart_5833448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833458 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_5833458 : Nat := 118140960795 + 5833458 * 2 ^ 59
def prefixEnd_5833458 : Nat := 4983230072969 + 3 ^ 40 * 5833458 * 2
def baseEnd_5833458 : Nat := 2995367831815542802447421

theorem tailTrace_5833458 : CollatzResearch.WordTrace tailWord_5833458 prefixEnd_5833458 2995367831815542802447421 := by
  unfold tailWord_5833458
  simp only [CollatzResearch.WordTrace]
  refine ⟨53190923125096354038495257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141842461666923610769320685 53190923125096354038495257)
  ·
    refine ⟨39893192343822265528871443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53190923125096354038495257 39893192343822265528871443)
    ·
      refine ⟨59839788515733398293307165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39893192343822265528871443 59839788515733398293307165)
      ·
        refine ⟨22439920693400024359990187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59839788515733398293307165 22439920693400024359990187)
        ·
          refine ⟨33659881040100036539985281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22439920693400024359990187 33659881040100036539985281)
          ·
            refine ⟨25244910780075027404988961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33659881040100036539985281 25244910780075027404988961)
            ·
              refine ⟨18933683085056270553741721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25244910780075027404988961 18933683085056270553741721)
              ·
                refine ⟨14200262313792202915306291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18933683085056270553741721 14200262313792202915306291)
                ·
                  refine ⟨21300393470688304372959437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14200262313792202915306291 21300393470688304372959437)
                  ·
                    refine ⟨7987647551508114139859789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21300393470688304372959437 7987647551508114139859789)
                    ·
                      refine ⟨2995367831815542802447421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7987647551508114139859789 2995367831815542802447421)
                      ·
                        rfl

theorem cell23_5833458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_5833458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833458 prefixEnd_5833458 := by exact prefixLift 5833458
  have htrace : WordTrace (prefixWord ++ tailWord_5833458) baseStart_5833458 baseEnd_5833458 := by
    simpa [prefixWord, tailWord_5833458, baseEnd_5833458] using wordTrace_append hprefix tailTrace_5833458
  have hstable : (prefixWord ++ tailWord_5833458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833458).length < 2 ^ (prefixWord ++ tailWord_5833458).sum := by decide
  have hdescent : baseEnd_5833458 < baseStart_5833458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833518 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5833518 : Nat := 118140960795 + 5833518 * 2 ^ 59
def prefixEnd_5833518 : Nat := 4983230072969 + 3 ^ 40 * 5833518 * 2
def baseEnd_5833518 : Nat := 2995398640654812567697145

theorem tailTrace_5833518 : CollatzResearch.WordTrace tailWord_5833518 prefixEnd_5833518 2995398640654812567697145 := by
  unfold tailWord_5833518
  simp only [CollatzResearch.WordTrace]
  refine ⟨26595735110021005800145651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141843920586778697600776805 26595735110021005800145651)
  ·
    refine ⟨39893602665031508700218477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26595735110021005800145651 39893602665031508700218477)
    ·
      refine ⟨14960100999386815762581929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39893602665031508700218477 14960100999386815762581929)
      ·
        refine ⟨11220075749540111821936447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14960100999386815762581929 11220075749540111821936447)
        ·
          refine ⟨16830113624310167732904671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220075749540111821936447 16830113624310167732904671)
          ·
            refine ⟨25245170436465251599357007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16830113624310167732904671 25245170436465251599357007)
            ·
              refine ⟨37867755654697877399035511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25245170436465251599357007 37867755654697877399035511)
              ·
                refine ⟨56801633482046816098553267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37867755654697877399035511 56801633482046816098553267)
                ·
                  refine ⟨85202450223070224147829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56801633482046816098553267 85202450223070224147829901)
                  ·
                    refine ⟨31950918833651334055436213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85202450223070224147829901 31950918833651334055436213)
                    ·
                      refine ⟨2995398640654812567697145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31950918833651334055436213 2995398640654812567697145)
                      ·
                        rfl

theorem cell23_5833518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5833518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833518 prefixEnd_5833518 := by exact prefixLift 5833518
  have htrace : WordTrace (prefixWord ++ tailWord_5833518) baseStart_5833518 baseEnd_5833518 := by
    simpa [prefixWord, tailWord_5833518, baseEnd_5833518] using wordTrace_append hprefix tailTrace_5833518
  have hstable : (prefixWord ++ tailWord_5833518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833518).length < 2 ^ (prefixWord ++ tailWord_5833518).sum := by decide
  have hdescent : baseEnd_5833518 < baseStart_5833518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833568 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_5833568 : Nat := 118140960795 + 5833568 * 2 ^ 59
def prefixEnd_5833568 : Nat := 4983230072969 + 3 ^ 40 * 5833568 * 2
def baseEnd_5833568 : Nat := 998474771562512457357305

theorem tailTrace_5833568 : CollatzResearch.WordTrace tailWord_5833568 prefixEnd_5833568 998474771562512457357305 := by
  unfold tailWord_5833568
  simp only [CollatzResearch.WordTrace]
  refine ⟨106383852264993452470242679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141845136353324603293656905 106383852264993452470242679)
  ·
    refine ⟨159575778397490178705364019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106383852264993452470242679 159575778397490178705364019)
    ·
      refine ⟨239363667596235268058046029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159575778397490178705364019 239363667596235268058046029)
      ·
        refine ⟨89761375348588225521767261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239363667596235268058046029 89761375348588225521767261)
        ·
          refine ⟨33660515755720584570662723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89761375348588225521767261 33660515755720584570662723)
          ·
            refine ⟨50490773633580876855994085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33660515755720584570662723 50490773633580876855994085)
            ·
              refine ⟨9467020056296414410498891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50490773633580876855994085 9467020056296414410498891)
              ·
                refine ⟨14200530084444621615748337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9467020056296414410498891 14200530084444621615748337)
                ·
                  refine ⟨10650397563333466211811253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14200530084444621615748337 10650397563333466211811253)
                  ·
                    refine ⟨998474771562512457357305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10650397563333466211811253 998474771562512457357305)
                    ·
                      rfl

theorem cell23_5833568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_5833568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833568 prefixEnd_5833568 := by exact prefixLift 5833568
  have htrace : WordTrace (prefixWord ++ tailWord_5833568) baseStart_5833568 baseEnd_5833568 := by
    simpa [prefixWord, tailWord_5833568, baseEnd_5833568] using wordTrace_append hprefix tailTrace_5833568
  have hstable : (prefixWord ++ tailWord_5833568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833568).length < 2 ^ (prefixWord ++ tailWord_5833568).sum := by decide
  have hdescent : baseEnd_5833568 < baseStart_5833568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833605 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_5833605 : Nat := 118140960795 + 5833605 * 2 ^ 59
def prefixEnd_5833605 : Nat := 4983230072969 + 3 ^ 40 * 5833605 * 2
def baseEnd_5833605 : Nat := 2995443313471753727309245

theorem tailTrace_5833605 : CollatzResearch.WordTrace tailWord_5833605 prefixEnd_5833605 2995443313471753727309245 := by
  unfold tailWord_5833605
  simp only [CollatzResearch.WordTrace]
  refine ⟨212769054030852860259582269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141846036020568573506388179 212769054030852860259582269)
  ·
    refine ⟨79788395261569822597343351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212769054030852860259582269 79788395261569822597343351)
    ·
      refine ⟨119682592892354733896015027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79788395261569822597343351 119682592892354733896015027)
      ·
        refine ⟨179523889338532100844022541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119682592892354733896015027 179523889338532100844022541)
        ·
          refine ⟨67321458501949537816508453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179523889338532100844022541 67321458501949537816508453)
          ·
            refine ⟨12622773469115538340595335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67321458501949537816508453 12622773469115538340595335)
            ·
              refine ⟨18934160203673307510893003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622773469115538340595335 18934160203673307510893003)
              ·
                refine ⟨28401240305509961266339505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18934160203673307510893003 28401240305509961266339505)
                ·
                  refine ⟨21300930229132470949754629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28401240305509961266339505 21300930229132470949754629)
                  ·
                    refine ⟨3993924417962338303078993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21300930229132470949754629 3993924417962338303078993)
                    ·
                      refine ⟨2995443313471753727309245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993924417962338303078993 2995443313471753727309245)
                      ·
                        rfl

theorem cell23_5833605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_5833605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833605 prefixEnd_5833605 := by exact prefixLift 5833605
  have htrace : WordTrace (prefixWord ++ tailWord_5833605) baseStart_5833605 baseEnd_5833605 := by
    simpa [prefixWord, tailWord_5833605, baseEnd_5833605] using wordTrace_append hprefix tailTrace_5833605
  have hstable : (prefixWord ++ tailWord_5833605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833605).length < 2 ^ (prefixWord ++ tailWord_5833605).sum := by decide
  have hdescent : baseEnd_5833605 < baseStart_5833605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833651 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_5833651 : Nat := 118140960795 + 5833651 * 2 ^ 59
def prefixEnd_5833651 : Nat := 4983230072969 + 3 ^ 40 * 5833651 * 2
def baseEnd_5833651 : Nat := 2995466933581860547334033

theorem tailTrace_5833651 : CollatzResearch.WordTrace tailWord_5833651 prefixEnd_5833651 2995466933581860547334033 := by
  unfold tailWord_5833651
  simp only [CollatzResearch.WordTrace]
  refine ⟨212770731788686210115756807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141847154525790806743837871 212770731788686210115756807)
  ·
    refine ⟨319156097683029315173635211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212770731788686210115756807 319156097683029315173635211)
    ·
      refine ⟨478734146524543972760452817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319156097683029315173635211 478734146524543972760452817)
      ·
        refine ⟨359050609893407979570339613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478734146524543972760452817 359050609893407979570339613)
        ·
          refine ⟨134643978710027992338877355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359050609893407979570339613 134643978710027992338877355)
          ·
            refine ⟨201965968065041988508316033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134643978710027992338877355 201965968065041988508316033)
            ·
              refine ⟨151474476048781491381237025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201965968065041988508316033 151474476048781491381237025)
              ·
                refine ⟨113605857036586118535927769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151474476048781491381237025 113605857036586118535927769)
                ·
                  refine ⟨85204392777439588901945827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113605857036586118535927769 85204392777439588901945827)
                  ·
                    refine ⟨127806589166159383352918741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85204392777439588901945827 127806589166159383352918741)
                    ·
                      refine ⟨2995466933581860547334033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127806589166159383352918741 2995466933581860547334033)
                      ·
                        rfl

theorem cell23_5833651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_5833651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833651 prefixEnd_5833651 := by exact prefixLift 5833651
  have htrace : WordTrace (prefixWord ++ tailWord_5833651) baseStart_5833651 baseEnd_5833651 := by
    simpa [prefixWord, tailWord_5833651, baseEnd_5833651] using wordTrace_append hprefix tailTrace_5833651
  have hstable : (prefixWord ++ tailWord_5833651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833651).length < 2 ^ (prefixWord ++ tailWord_5833651).sum := by decide
  have hdescent : baseEnd_5833651 < baseStart_5833651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833655 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_5833655 : Nat := 118140960795 + 5833655 * 2 ^ 59
def prefixEnd_5833655 : Nat := 4983230072969 + 3 ^ 40 * 5833655 * 2
def baseEnd_5833655 : Nat := 2995468987504478531684015

theorem tailTrace_5833655 : CollatzResearch.WordTrace tailWord_5833655 prefixEnd_5833655 2995468987504478531684015 := by
  unfold tailWord_5833655
  simp only [CollatzResearch.WordTrace]
  refine ⟨212770877680671718798902419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141847251787114479199268279 212770877680671718798902419)
  ·
    refine ⟨319156316521007578198353629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212770877680671718798902419 319156316521007578198353629)
    ·
      refine ⟨119683618695377841824382611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319156316521007578198353629 119683618695377841824382611)
      ·
        refine ⟨179525428043066762736573917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119683618695377841824382611 179525428043066762736573917)
        ·
          refine ⟨67322035516150036026215219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179525428043066762736573917 67322035516150036026215219)
          ·
            refine ⟨100983053274225054039322829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67322035516150036026215219 100983053274225054039322829)
            ·
              refine ⟨37868644977834395264746061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100983053274225054039322829 37868644977834395264746061)
              ·
                refine ⟨14200741866687898224279773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37868644977834395264746061 14200741866687898224279773)
                ·
                  refine ⟨5325278200007961834104915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14200741866687898224279773 5325278200007961834104915)
                  ·
                    refine ⟨7987917300011942751157373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325278200007961834104915 7987917300011942751157373)
                    ·
                      refine ⟨2995468987504478531684015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7987917300011942751157373 2995468987504478531684015)
                      ·
                        rfl

theorem cell23_5833655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_5833655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833655 prefixEnd_5833655 := by exact prefixLift 5833655
  have htrace : WordTrace (prefixWord ++ tailWord_5833655) baseStart_5833655 baseEnd_5833655 := by
    simpa [prefixWord, tailWord_5833655, baseEnd_5833655] using wordTrace_append hprefix tailTrace_5833655
  have hstable : (prefixWord ++ tailWord_5833655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833655).length < 2 ^ (prefixWord ++ tailWord_5833655).sum := by decide
  have hdescent : baseEnd_5833655 < baseStart_5833655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833675 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 1, 5]
def baseStart_5833675 : Nat := 118140960795 + 5833675 * 2 ^ 59
def prefixEnd_5833675 : Nat := 4983230072969 + 3 ^ 40 * 5833675 * 2
def baseEnd_5833675 : Nat := 998493085705856151144641

theorem tailTrace_5833675 : CollatzResearch.WordTrace tailWord_5833675 prefixEnd_5833675 998493085705856151144641 := by
  unfold tailWord_5833675
  simp only [CollatzResearch.WordTrace]
  refine ⟨212771607140599262214630479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141847738093732841476420319 212771607140599262214630479)
  ·
    refine ⟨319157410710898893321945719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212771607140599262214630479 319157410710898893321945719)
    ·
      refine ⟨478736116066348339982918579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319157410710898893321945719 478736116066348339982918579)
      ·
        refine ⟨718104174099522509974377869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478736116066348339982918579 718104174099522509974377869)
        ·
          refine ⟨269289065287320941240391701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 718104174099522509974377869 269289065287320941240391701)
          ·
            refine ⟨12622924935343169120643361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269289065287320941240391701 12622924935343169120643361)
            ·
              refine ⟨9467193701507376840482521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12622924935343169120643361 9467193701507376840482521)
              ·
                refine ⟨7100395276130532630361891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9467193701507376840482521 7100395276130532630361891)
                ·
                  refine ⟨10650592914195798945542837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100395276130532630361891 10650592914195798945542837)
                  ·
                    refine ⟨998493085705856151144641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10650592914195798945542837 998493085705856151144641)
                    ·
                      rfl

theorem cell23_5833675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 5].length) (baseStart_5833675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833675 prefixEnd_5833675 := by exact prefixLift 5833675
  have htrace : WordTrace (prefixWord ++ tailWord_5833675) baseStart_5833675 baseEnd_5833675 := by
    simpa [prefixWord, tailWord_5833675, baseEnd_5833675] using wordTrace_append hprefix tailTrace_5833675
  have hstable : (prefixWord ++ tailWord_5833675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833675).length < 2 ^ (prefixWord ++ tailWord_5833675).sum := by decide
  have hdescent : baseEnd_5833675 < baseStart_5833675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833682 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5833682 : Nat := 118140960795 + 5833682 * 2 ^ 59
def prefixEnd_5833682 : Nat := 4983230072969 + 3 ^ 40 * 5833682 * 2
def baseEnd_5833682 : Nat := 2995482851482149926046391

theorem tailTrace_5833682 : CollatzResearch.WordTrace tailWord_5833682 prefixEnd_5833682 2995482851482149926046391 := by
  unfold tailWord_5833682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53192965612893475602533825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141847908301049268273423533 53192965612893475602533825)
  ·
    refine ⟨39894724209670106701900369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53192965612893475602533825 39894724209670106701900369)
    ·
      refine ⟨29921043157252580026425277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39894724209670106701900369 29921043157252580026425277)
      ·
        refine ⟨11220391183969717509909479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29921043157252580026425277 11220391183969717509909479)
        ·
          refine ⟨16830586775954576264864219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220391183969717509909479 16830586775954576264864219)
          ·
            refine ⟨25245880163931864397296329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16830586775954576264864219 25245880163931864397296329)
            ·
              refine ⟨18934410122948898297972247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25245880163931864397296329 18934410122948898297972247)
              ·
                refine ⟨28401615184423347446958371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18934410122948898297972247 28401615184423347446958371)
                ·
                  refine ⟨42602422776635021170437557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28401615184423347446958371 42602422776635021170437557)
                  ·
                    refine ⟨3993977135309533234728521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42602422776635021170437557 3993977135309533234728521)
                    ·
                      refine ⟨2995482851482149926046391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3993977135309533234728521 2995482851482149926046391)
                      ·
                        rfl

theorem cell23_5833682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5833682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833682 prefixEnd_5833682 := by exact prefixLift 5833682
  have htrace : WordTrace (prefixWord ++ tailWord_5833682) baseStart_5833682 baseEnd_5833682 := by
    simpa [prefixWord, tailWord_5833682, baseEnd_5833682] using wordTrace_append hprefix tailTrace_5833682
  have hstable : (prefixWord ++ tailWord_5833682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833682).length < 2 ^ (prefixWord ++ tailWord_5833682).sum := by decide
  have hdescent : baseEnd_5833682 < baseStart_5833682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833689 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 1, 1, 3]
def baseStart_5833689 : Nat := 118140960795 + 5833689 * 2 ^ 59
def prefixEnd_5833689 : Nat := 4983230072969 + 3 ^ 40 * 5833689 * 2
def baseEnd_5833689 : Nat := 2995486445846731398658859

theorem tailTrace_5833689 : CollatzResearch.WordTrace tailWord_5833689 prefixEnd_5833689 2995486445846731398658859 := by
  unfold tailWord_5833689
  simp only [CollatzResearch.WordTrace]
  refine ⟨212772117762548542605640121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141848078508365695070426747 212772117762548542605640121)
  ·
    refine ⟨159579088321911406954230091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212772117762548542605640121 159579088321911406954230091)
    ·
      refine ⟨239368632482867110431345137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159579088321911406954230091 239368632482867110431345137)
      ·
        refine ⟨179526474362150332823508853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239368632482867110431345137 179526474362150332823508853)
        ·
          refine ⟨16830606971451593702203955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179526474362150332823508853 16830606971451593702203955)
          ·
            refine ⟨25245910457177390553305933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16830606971451593702203955 25245910457177390553305933)
            ·
              refine ⟨9467216421441521457489725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25245910457177390553305933 9467216421441521457489725)
              ·
                refine ⟨3550206158040570546558647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9467216421441521457489725 3550206158040570546558647)
                ·
                  refine ⟨5325309237060855819837971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550206158040570546558647 5325309237060855819837971)
                  ·
                    refine ⟨7987963855591283729756957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325309237060855819837971 7987963855591283729756957)
                    ·
                      refine ⟨2995486445846731398658859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7987963855591283729756957 2995486445846731398658859)
                      ·
                        rfl

theorem cell23_5833689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_5833689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833689 prefixEnd_5833689 := by exact prefixLift 5833689
  have htrace : WordTrace (prefixWord ++ tailWord_5833689) baseStart_5833689 baseEnd_5833689 := by
    simpa [prefixWord, tailWord_5833689, baseEnd_5833689] using wordTrace_append hprefix tailTrace_5833689
  have hstable : (prefixWord ++ tailWord_5833689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833689).length < 2 ^ (prefixWord ++ tailWord_5833689).sum := by decide
  have hdescent : baseEnd_5833689 < baseStart_5833689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833706 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_5833706 : Nat := 118140960795 + 5833706 * 2 ^ 59
def prefixEnd_5833706 : Nat := 4983230072969 + 3 ^ 40 * 5833706 * 2
def baseEnd_5833706 : Nat := 2995495175017857832146281

theorem tailTrace_5833706 : CollatzResearch.WordTrace tailWord_5833706 prefixEnd_5833706 2995495175017857832146281 := by
  unfold tailWord_5833706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53193184450871738627252243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141848491868991303006005981 53193184450871738627252243)
  ·
    refine ⟨79789776676307607940878365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53193184450871738627252243 79789776676307607940878365)
    ·
      refine ⟨29921166253615352977829387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79789776676307607940878365 29921166253615352977829387)
      ·
        refine ⟨44881749380423029466744081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29921166253615352977829387 44881749380423029466744081)
        ·
          refine ⟨33661312035317272100058061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44881749380423029466744081 33661312035317272100058061)
          ·
            refine ⟨12622992013243977037521773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33661312035317272100058061 12622992013243977037521773)
            ·
              refine ⟨4733622004966491389070665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12622992013243977037521773 4733622004966491389070665)
              ·
                refine ⟨3550216503724868541802999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733622004966491389070665 3550216503724868541802999)
                ·
                  refine ⟨5325324755587302812704499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550216503724868541802999 5325324755587302812704499)
                  ·
                    refine ⟨7987987133380954219056749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325324755587302812704499 7987987133380954219056749)
                    ·
                      refine ⟨2995495175017857832146281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7987987133380954219056749 2995495175017857832146281)
                      ·
                        rfl

theorem cell23_5833706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_5833706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833706 prefixEnd_5833706 := by exact prefixLift 5833706
  have htrace : WordTrace (prefixWord ++ tailWord_5833706) baseStart_5833706 baseEnd_5833706 := by
    simpa [prefixWord, tailWord_5833706, baseEnd_5833706] using wordTrace_append hprefix tailTrace_5833706
  have hstable : (prefixWord ++ tailWord_5833706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833706).length < 2 ^ (prefixWord ++ tailWord_5833706).sum := by decide
  have hdescent : baseEnd_5833706 < baseStart_5833706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833726 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5833726 : Nat := 118140960795 + 5833726 * 2 ^ 59
def prefixEnd_5833726 : Nat := 4983230072969 + 3 ^ 40 * 5833726 * 2
def baseEnd_5833726 : Nat := 998501814876982584632063

theorem tailTrace_5833726 : CollatzResearch.WordTrace tailWord_5833726 prefixEnd_5833726 998501814876982584632063 := by
  unfold tailWord_5833726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26596683407926812240592129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141848978175609665283158021 26596683407926812240592129)
  ·
    refine ⟨19947512555945109180444097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26596683407926812240592129 19947512555945109180444097)
    ·
      refine ⟨14960634416958831885333073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19947512555945109180444097 14960634416958831885333073)
      ·
        refine ⟨11220475812719123913999805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14960634416958831885333073 11220475812719123913999805)
        ·
          refine ⟨4207678429769671467749927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11220475812719123913999805 4207678429769671467749927)
          ·
            refine ⟨6311517644654507201624891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207678429769671467749927 6311517644654507201624891)
            ·
              refine ⟨9467276466981760802437337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311517644654507201624891 9467276466981760802437337)
              ·
                refine ⟨7100457350236320601828003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9467276466981760802437337 7100457350236320601828003)
                ·
                  refine ⟨10650686025354480902742005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100457350236320601828003 10650686025354480902742005)
                  ·
                    refine ⟨998501814876982584632063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10650686025354480902742005 998501814876982584632063)
                    ·
                      rfl

theorem cell23_5833726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5833726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833726 prefixEnd_5833726 := by exact prefixLift 5833726
  have htrace : WordTrace (prefixWord ++ tailWord_5833726) baseStart_5833726 baseEnd_5833726 := by
    simpa [prefixWord, tailWord_5833726, baseEnd_5833726] using wordTrace_append hprefix tailTrace_5833726
  have hstable : (prefixWord ++ tailWord_5833726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833726).length < 2 ^ (prefixWord ++ tailWord_5833726).sum := by decide
  have hdescent : baseEnd_5833726 < baseStart_5833726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833745 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_5833745 : Nat := 118140960795 + 5833745 * 2 ^ 59
def prefixEnd_5833745 : Nat := 4983230072969 + 3 ^ 40 * 5833745 * 2
def baseEnd_5833745 : Nat := 2995515200763383179558601

theorem tailTrace_5833745 : CollatzResearch.WordTrace tailWord_5833745 prefixEnd_5833745 2995515200763383179558601 := by
  unfold tailWord_5833745
  simp only [CollatzResearch.WordTrace]
  refine ⟨212774160250345664169678689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141849440166897109446452459 212774160250345664169678689)
  ·
    refine ⟨159580620187759248127259017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212774160250345664169678689 159580620187759248127259017)
    ·
      refine ⟨119685465140819436095444263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159580620187759248127259017 119685465140819436095444263)
      ·
        refine ⟨179528197711229154143166395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119685465140819436095444263 179528197711229154143166395)
        ·
          refine ⟨269292296566843731214749593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179528197711229154143166395 269292296566843731214749593)
          ·
            refine ⟨201969222425132798411062195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269292296566843731214749593 201969222425132798411062195)
            ·
              refine ⟨302953833637699197616593293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201969222425132798411062195 302953833637699197616593293)
              ·
                refine ⟨113607687614137199106222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302953833637699197616593293 113607687614137199106222485)
                ·
                  refine ⟨5325360356912681208104179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113607687614137199106222485 5325360356912681208104179)
                  ·
                    refine ⟨7988040535369021812156269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325360356912681208104179 7988040535369021812156269)
                    ·
                      refine ⟨2995515200763383179558601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988040535369021812156269 2995515200763383179558601)
                      ·
                        rfl

theorem cell23_5833745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_5833745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833745 prefixEnd_5833745 := by exact prefixLift 5833745
  have htrace : WordTrace (prefixWord ++ tailWord_5833745) baseStart_5833745 baseEnd_5833745 := by
    simpa [prefixWord, tailWord_5833745, baseEnd_5833745] using wordTrace_append hprefix tailTrace_5833745
  have hstable : (prefixWord ++ tailWord_5833745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833745).length < 2 ^ (prefixWord ++ tailWord_5833745).sum := by decide
  have hdescent : baseEnd_5833745 < baseStart_5833745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833749 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_5833749 : Nat := 118140960795 + 5833749 * 2 ^ 59
def prefixEnd_5833749 : Nat := 4983230072969 + 3 ^ 40 * 5833749 * 2
def baseEnd_5833749 : Nat := 2995517254686001163908583

theorem tailTrace_5833749 : CollatzResearch.WordTrace tailWord_5833749 prefixEnd_5833749 2995517254686001163908583 := by
  unfold tailWord_5833749
  simp only [CollatzResearch.WordTrace]
  refine ⟨212774306142331172852824301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141849537428220781901882867 212774306142331172852824301)
  ·
    refine ⟨79790364803374189819809113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212774306142331172852824301 79790364803374189819809113)
    ·
      refine ⟨59842773602530642364856835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79790364803374189819809113 59842773602530642364856835)
      ·
        refine ⟨89764160403795963547285253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59842773602530642364856835 89764160403795963547285253)
        ·
          refine ⟨16830780075711743165115985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89764160403795963547285253 16830780075711743165115985)
          ·
            refine ⟨12623085056783807373836989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16830780075711743165115985 12623085056783807373836989)
            ·
              refine ⟨4733656896293927765188871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12623085056783807373836989 4733656896293927765188871)
              ·
                refine ⟨7100485344440891647783307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733656896293927765188871 7100485344440891647783307)
                ·
                  refine ⟨10650728016661337471674961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100485344440891647783307 10650728016661337471674961)
                  ·
                    refine ⟨7988046012496003103756221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10650728016661337471674961 7988046012496003103756221)
                    ·
                      refine ⟨2995517254686001163908583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988046012496003103756221 2995517254686001163908583)
                      ·
                        rfl

theorem cell23_5833749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_5833749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833749 prefixEnd_5833749 := by exact prefixLift 5833749
  have htrace : WordTrace (prefixWord ++ tailWord_5833749) baseStart_5833749 baseEnd_5833749 := by
    simpa [prefixWord, tailWord_5833749, baseEnd_5833749] using wordTrace_append hprefix tailTrace_5833749
  have hstable : (prefixWord ++ tailWord_5833749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833749).length < 2 ^ (prefixWord ++ tailWord_5833749).sum := by decide
  have hdescent : baseEnd_5833749 < baseStart_5833749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833763 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 1, 2, 2]
def baseStart_5833763 : Nat := 118140960795 + 5833763 * 2 ^ 59
def prefixEnd_5833763 : Nat := 4983230072969 + 3 ^ 40 * 5833763 * 2
def baseEnd_5833763 : Nat := 2995524443415164109133519

theorem tailTrace_5833763 : CollatzResearch.WordTrace tailWord_5833763 prefixEnd_5833763 2995524443415164109133519 := by
  unfold tailWord_5833763
  simp only [CollatzResearch.WordTrace]
  refine ⟨212774816764280453243833943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141849877842853635495889295 212774816764280453243833943)
  ·
    refine ⟨319162225146420679865750915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212774816764280453243833943 319162225146420679865750915)
    ·
      refine ⟨478743337719631019798626373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319162225146420679865750915 478743337719631019798626373)
      ·
        refine ⟨89764375822430816212242445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 478743337719631019798626373 89764375822430816212242445)
        ·
          refine ⟨33661640933411556079590917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89764375822430816212242445 33661640933411556079590917)
          ·
            refine ⟨6311557675014666764923297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33661640933411556079590917 6311557675014666764923297)
            ·
              refine ⟨4733668256261000073692473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6311557675014666764923297 4733668256261000073692473)
              ·
                refine ⟨3550251192195750055269355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733668256261000073692473 3550251192195750055269355)
                ·
                  refine ⟨5325376788293625082904033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550251192195750055269355 5325376788293625082904033)
                  ·
                    refine ⟨3994032591220218812178025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325376788293625082904033 3994032591220218812178025)
                    ·
                      refine ⟨2995524443415164109133519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994032591220218812178025 2995524443415164109133519)
                      ·
                        rfl

theorem cell23_5833763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_5833763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833763 prefixEnd_5833763 := by exact prefixLift 5833763
  have htrace : WordTrace (prefixWord ++ tailWord_5833763) baseStart_5833763 baseEnd_5833763 := by
    simpa [prefixWord, tailWord_5833763, baseEnd_5833763] using wordTrace_append hprefix tailTrace_5833763
  have hstable : (prefixWord ++ tailWord_5833763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833763).length < 2 ^ (prefixWord ++ tailWord_5833763).sum := by decide
  have hdescent : baseEnd_5833763 < baseStart_5833763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833802 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_5833802 : Nat := 118140960795 + 5833802 * 2 ^ 59
def prefixEnd_5833802 : Nat := 4983230072969 + 3 ^ 40 * 5833802 * 2
def baseEnd_5833802 : Nat := 2995544469160689456545839

theorem tailTrace_5833802 : CollatzResearch.WordTrace tailWord_5833802 prefixEnd_5833802 2995544469160689456545839 := by
  unfold tailWord_5833802
  simp only [CollatzResearch.WordTrace]
  refine ⟨53194059802784790726125915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141850826140759441936335773 53194059802784790726125915)
  ·
    refine ⟨79791089704177186089188873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53194059802784790726125915 79791089704177186089188873)
    ·
      refine ⟨59843317278132889566891655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79791089704177186089188873 59843317278132889566891655)
      ·
        refine ⟨89764975917199334350337483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59843317278132889566891655 89764975917199334350337483)
        ·
          refine ⟨134647463875799001525506225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89764975917199334350337483 134647463875799001525506225)
          ·
            refine ⟨100985597906849251144129669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134647463875799001525506225 100985597906849251144129669)
            ·
              refine ⟨18934799607534234589524313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100985597906849251144129669 18934799607534234589524313)
              ·
                refine ⟨14201099705650675942143235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18934799607534234589524313 14201099705650675942143235)
                ·
                  refine ⟨21301649558476013913214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14201099705650675942143235 21301649558476013913214853)
                  ·
                    refine ⟨3994059292214252608727785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21301649558476013913214853 3994059292214252608727785)
                    ·
                      refine ⟨2995544469160689456545839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994059292214252608727785 2995544469160689456545839)
                      ·
                        rfl

theorem cell23_5833802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_5833802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833802 prefixEnd_5833802 := by exact prefixLift 5833802
  have htrace : WordTrace (prefixWord ++ tailWord_5833802) baseStart_5833802 baseEnd_5833802 := by
    simpa [prefixWord, tailWord_5833802, baseEnd_5833802] using wordTrace_append hprefix tailTrace_5833802
  have hstable : (prefixWord ++ tailWord_5833802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833802).length < 2 ^ (prefixWord ++ tailWord_5833802).sum := by decide
  have hdescent : baseEnd_5833802 < baseStart_5833802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833818 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_5833818 : Nat := 118140960795 + 5833818 * 2 ^ 59
def prefixEnd_5833818 : Nat := 4983230072969 + 3 ^ 40 * 5833818 * 2
def baseEnd_5833818 : Nat := 2995552684851161393945765

theorem tailTrace_5833818 : CollatzResearch.WordTrace tailWord_5833818 prefixEnd_5833818 2995552684851161393945765 := by
  unfold tailWord_5833818
  simp only [CollatzResearch.WordTrace]
  refine ⟨53194205694770299409271527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141851215186054131758057405 53194205694770299409271527)
  ·
    refine ⟨79791308542155449113907291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53194205694770299409271527 79791308542155449113907291)
    ·
      refine ⟨119686962813233173670860937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79791308542155449113907291 119686962813233173670860937)
      ·
        refine ⟨89765222109924880253145703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119686962813233173670860937 89765222109924880253145703)
        ·
          refine ⟨134647833164887320379718555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89765222109924880253145703 134647833164887320379718555)
          ·
            refine ⟨201971749747330980569577833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134647833164887320379718555 201971749747330980569577833)
            ·
              refine ⟨151478812310498235427183375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201971749747330980569577833 151478812310498235427183375)
              ·
                refine ⟨227218218465747353140775063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151478812310498235427183375 227218218465747353140775063)
                ·
                  refine ⟨340827327698621029711162595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227218218465747353140775063 340827327698621029711162595)
                  ·
                    refine ⟨511240991547931544566743893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340827327698621029711162595 511240991547931544566743893)
                    ·
                      refine ⟨2995552684851161393945765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 511240991547931544566743893 2995552684851161393945765)
                      ·
                        rfl

theorem cell23_5833818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_5833818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833818 prefixEnd_5833818 := by exact prefixLift 5833818
  have htrace : WordTrace (prefixWord ++ tailWord_5833818) baseStart_5833818 baseEnd_5833818 := by
    simpa [prefixWord, tailWord_5833818, baseEnd_5833818] using wordTrace_append hprefix tailTrace_5833818
  have hstable : (prefixWord ++ tailWord_5833818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833818).length < 2 ^ (prefixWord ++ tailWord_5833818).sum := by decide
  have hdescent : baseEnd_5833818 < baseStart_5833818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833836 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_5833836 : Nat := 118140960795 + 5833836 * 2 ^ 59
def prefixEnd_5833836 : Nat := 4983230072969 + 3 ^ 40 * 5833836 * 2
def baseEnd_5833836 : Nat := 2995561927502942323520683

theorem tailTrace_5833836 : CollatzResearch.WordTrace tailWord_5833836 prefixEnd_5833836 2995561927502942323520683 := by
  unfold tailWord_5833836
  simp only [CollatzResearch.WordTrace]
  refine ⟨106388739646507993355620681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141851652862010657807494241 106388739646507993355620681)
  ·
    refine ⟨79791554734880995016715511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106388739646507993355620681 79791554734880995016715511)
    ·
      refine ⟨119687332102321492525073267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79791554734880995016715511 119687332102321492525073267)
      ·
        refine ⟨179530998153482238787609901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119687332102321492525073267 179530998153482238787609901)
        ·
          refine ⟨67324124307555839545353713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179530998153482238787609901 67324124307555839545353713)
          ·
            refine ⟨50493093230666879659015285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67324124307555839545353713 50493093230666879659015285)
            ·
              refine ⟨4733727490375019968032683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50493093230666879659015285 4733727490375019968032683)
              ·
                refine ⟨7100591235562529952049025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733727490375019968032683 7100591235562529952049025)
                ·
                  refine ⟨5325443426671897464036769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7100591235562529952049025 5325443426671897464036769)
                  ·
                    refine ⟨3994082570003923098027577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325443426671897464036769 3994082570003923098027577)
                    ·
                      refine ⟨2995561927502942323520683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994082570003923098027577 2995561927502942323520683)
                      ·
                        rfl

theorem cell23_5833836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_5833836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833836 prefixEnd_5833836 := by exact prefixLift 5833836
  have htrace : WordTrace (prefixWord ++ tailWord_5833836) baseStart_5833836 baseEnd_5833836 := by
    simpa [prefixWord, tailWord_5833836, baseEnd_5833836] using wordTrace_append hprefix tailTrace_5833836
  have hstable : (prefixWord ++ tailWord_5833836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833836).length < 2 ^ (prefixWord ++ tailWord_5833836).sum := by decide
  have hdescent : baseEnd_5833836 < baseStart_5833836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833875 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4]
def baseStart_5833875 : Nat := 118140960795 + 5833875 * 2 ^ 59
def prefixEnd_5833875 : Nat := 4983230072969 + 3 ^ 40 * 5833875 * 2
def baseEnd_5833875 : Nat := 2995581953248467670933003

theorem tailTrace_5833875 : CollatzResearch.WordTrace tailWord_5833875 prefixEnd_5833875 2995581953248467670933003 := by
  unfold tailWord_5833875
  simp only [CollatzResearch.WordTrace]
  refine ⟨212778901739874696371911079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141852601159916464247940719 212778901739874696371911079)
  ·
    refine ⟨319168352609812044557866619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212778901739874696371911079 319168352609812044557866619)
    ·
      refine ⟨478752528914718066836799929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319168352609812044557866619 478752528914718066836799929)
      ·
        refine ⟨359064396686038550127599947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478752528914718066836799929 359064396686038550127599947)
        ·
          refine ⟨538596595029057825191399921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359064396686038550127599947 538596595029057825191399921)
          ·
            refine ⟨403947446271793368893549941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538596595029057825191399921 403947446271793368893549941)
            ·
              refine ⟨37870073087980628333770307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 403947446271793368893549941 37870073087980628333770307)
              ·
                refine ⟨56805109631970942500655461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37870073087980628333770307 56805109631970942500655461)
                ·
                  refine ⟨10650958055994551718872899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56805109631970942500655461 10650958055994551718872899)
                  ·
                    refine ⟨15976437083991827578309349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10650958055994551718872899 15976437083991827578309349)
                    ·
                      refine ⟨2995581953248467670933003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15976437083991827578309349 2995581953248467670933003)
                      ·
                        rfl

theorem cell23_5833875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_5833875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833875 prefixEnd_5833875 := by exact prefixLift 5833875
  have htrace : WordTrace (prefixWord ++ tailWord_5833875) baseStart_5833875 baseEnd_5833875 := by
    simpa [prefixWord, tailWord_5833875, baseEnd_5833875] using wordTrace_append hprefix tailTrace_5833875
  have hstable : (prefixWord ++ tailWord_5833875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833875).length < 2 ^ (prefixWord ++ tailWord_5833875).sum := by decide
  have hdescent : baseEnd_5833875 < baseStart_5833875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833882 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5833882 : Nat := 118140960795 + 5833882 * 2 ^ 59
def prefixEnd_5833882 : Nat := 4983230072969 + 3 ^ 40 * 5833882 * 2
def baseEnd_5833882 : Nat := 2995585547613049143545471

theorem tailTrace_5833882 : CollatzResearch.WordTrace tailWord_5833882 prefixEnd_5833882 2995585547613049143545471 := by
  unfold tailWord_5833882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53194789262712334141853975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141852771367232891044943933 53194789262712334141853975)
  ·
    refine ⟨79792183894068501212780963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53194789262712334141853975 79792183894068501212780963)
    ·
      refine ⟨119688275841102751819171445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79792183894068501212780963 119688275841102751819171445)
      ·
        refine ⟨11220775860103382983047323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119688275841102751819171445 11220775860103382983047323)
        ·
          refine ⟨16831163790155074474570985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220775860103382983047323 16831163790155074474570985)
          ·
            refine ⟨12623372842616305855928239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16831163790155074474570985 12623372842616305855928239)
            ·
              refine ⟨18935059263924458783892359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12623372842616305855928239 18935059263924458783892359)
              ·
                refine ⟨28402588895886688175838539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18935059263924458783892359 28402588895886688175838539)
                ·
                  refine ⟨42603883343830032263757809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28402588895886688175838539 42603883343830032263757809)
                  ·
                    refine ⟨31952912507872524197818357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42603883343830032263757809 31952912507872524197818357)
                    ·
                      refine ⟨2995585547613049143545471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31952912507872524197818357 2995585547613049143545471)
                      ·
                        rfl

theorem cell23_5833882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5833882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833882 prefixEnd_5833882 := by exact prefixLift 5833882
  have htrace : WordTrace (prefixWord ++ tailWord_5833882) baseStart_5833882 baseEnd_5833882 := by
    simpa [prefixWord, tailWord_5833882, baseEnd_5833882] using wordTrace_append hprefix tailTrace_5833882
  have hstable : (prefixWord ++ tailWord_5833882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833882).length < 2 ^ (prefixWord ++ tailWord_5833882).sum := by decide
  have hdescent : baseEnd_5833882 < baseStart_5833882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5833962 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_5833962 : Nat := 118140960795 + 5833962 * 2 ^ 59
def prefixEnd_5833962 : Nat := 4983230072969 + 3 ^ 40 * 5833962 * 2
def baseEnd_5833962 : Nat := 998542208688469610181701

theorem tailTrace_5833962 : CollatzResearch.WordTrace tailWord_5833962 prefixEnd_5833962 998542208688469610181701 := by
  unfold tailWord_5833962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53195518722639877557582035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141854716593706340153552093 53195518722639877557582035)
  ·
    refine ⟨79793278083959816336373053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53195518722639877557582035 79793278083959816336373053)
    ·
      refine ⟨29922479281484931126139895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79793278083959816336373053 29922479281484931126139895)
      ·
        refine ⟨44883718922227396689209843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29922479281484931126139895 44883718922227396689209843)
        ·
          refine ⟨67325578383341095033814765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44883718922227396689209843 67325578383341095033814765)
          ·
            refine ⟨25247091893752910637680537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67325578383341095033814765 25247091893752910637680537)
            ·
              refine ⟨18935318920314682978260403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25247091893752910637680537 18935318920314682978260403)
              ·
                refine ⟨28402978380472024467390605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18935318920314682978260403 28402978380472024467390605)
                ·
                  refine ⟨10651116892677009175271477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28402978380472024467390605 10651116892677009175271477)
                  ·
                    refine ⟨998542208688469610181701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10651116892677009175271477 998542208688469610181701)
                    ·
                      rfl

theorem cell23_5833962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_5833962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5833962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5833962 prefixEnd_5833962 := by exact prefixLift 5833962
  have htrace : WordTrace (prefixWord ++ tailWord_5833962) baseStart_5833962 baseEnd_5833962 := by
    simpa [prefixWord, tailWord_5833962, baseEnd_5833962] using wordTrace_append hprefix tailTrace_5833962
  have hstable : (prefixWord ++ tailWord_5833962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5833962).length < 2 ^ (prefixWord ++ tailWord_5833962).sum := by decide
  have hdescent : baseEnd_5833962 < baseStart_5833962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5833962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834005 : List Nat := [1, 3, 2, 1, 2, 1, 1, 12]
def baseStart_5834005 : Nat := 118140960795 + 5834005 * 2 ^ 59
def prefixEnd_5834005 : Nat := 4983230072969 + 3 ^ 40 * 5834005 * 2
def baseEnd_5834005 : Nat := 110949952064205635641015

theorem tailTrace_5834005 : CollatzResearch.WordTrace tailWord_5834005 prefixEnd_5834005 110949952064205635641015 := by
  unfold tailWord_5834005
  simp only [CollatzResearch.WordTrace]
  refine ⟨212783643229403728574143469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141855762152935819049428979 212783643229403728574143469)
  ·
    refine ⟨79793866211026398215303801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212783643229403728574143469 79793866211026398215303801)
    ·
      refine ⟨59845399658269798661477851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79793866211026398215303801 59845399658269798661477851)
      ·
        refine ⟨89768099487404697992216777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59845399658269798661477851 89768099487404697992216777)
        ·
          refine ⟨67326074615553523494162583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89768099487404697992216777 67326074615553523494162583)
          ·
            refine ⟨100989111923330285241243875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67326074615553523494162583 100989111923330285241243875)
            ·
              refine ⟨151483667884995427861865813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100989111923330285241243875 151483667884995427861865813)
              ·
                refine ⟨110949952064205635641015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 151483667884995427861865813 110949952064205635641015)
                ·
                  rfl

theorem cell23_5834005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 12].length) (baseStart_5834005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834005 prefixEnd_5834005 := by exact prefixLift 5834005
  have htrace : WordTrace (prefixWord ++ tailWord_5834005) baseStart_5834005 baseEnd_5834005 := by
    simpa [prefixWord, tailWord_5834005, baseEnd_5834005] using wordTrace_append hprefix tailTrace_5834005
  have hstable : (prefixWord ++ tailWord_5834005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834005).length < 2 ^ (prefixWord ++ tailWord_5834005).sum := by decide
  have hdescent : baseEnd_5834005 < baseStart_5834005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834016 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5834016 : Nat := 118140960795 + 5834016 * 2 ^ 59
def prefixEnd_5834016 : Nat := 4983230072969 + 3 ^ 40 * 5834016 * 2
def baseEnd_5834016 : Nat := 2995654354020751619269855

theorem tailTrace_5834016 : CollatzResearch.WordTrace tailWord_5834016 prefixEnd_5834016 2995654354020751619269855 := by
  unfold tailWord_5834016
  simp only [CollatzResearch.WordTrace]
  refine ⟨106392022216181938726396951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141856029621575918301862601 106392022216181938726396951)
  ·
    refine ⟨159588033324272908089595427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106392022216181938726396951 159588033324272908089595427)
    ·
      refine ⟨239382049986409362134393141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159588033324272908089595427 239382049986409362134393141)
      ·
        refine ⟨22442067186225877700099357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239382049986409362134393141 22442067186225877700099357)
        ·
          refine ⟨8415775194834704137537259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22442067186225877700099357 8415775194834704137537259)
          ·
            refine ⟨12623662792252056206305889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415775194834704137537259 12623662792252056206305889)
            ·
              refine ⟨9467747094189042154729417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12623662792252056206305889 9467747094189042154729417)
              ·
                refine ⟨7100810320641781616047063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9467747094189042154729417 7100810320641781616047063)
                ·
                  refine ⟨10651215480962672424070595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100810320641781616047063 10651215480962672424070595)
                  ·
                    refine ⟨15976823221444008636105893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10651215480962672424070595 15976823221444008636105893)
                    ·
                      refine ⟨2995654354020751619269855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15976823221444008636105893 2995654354020751619269855)
                      ·
                        rfl

theorem cell23_5834016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5834016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834016 prefixEnd_5834016 := by exact prefixLift 5834016
  have htrace : WordTrace (prefixWord ++ tailWord_5834016) baseStart_5834016 baseEnd_5834016 := by
    simpa [prefixWord, tailWord_5834016, baseEnd_5834016] using wordTrace_append hprefix tailTrace_5834016
  have hstable : (prefixWord ++ tailWord_5834016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834016).length < 2 ^ (prefixWord ++ tailWord_5834016).sum := by decide
  have hdescent : baseEnd_5834016 < baseStart_5834016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834019 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 3]
def baseStart_5834019 : Nat := 118140960795 + 5834019 * 2 ^ 59
def prefixEnd_5834019 : Nat := 4983230072969 + 3 ^ 40 * 5834019 * 2
def baseEnd_5834019 : Nat := 2995655894462715107532341

theorem tailTrace_5834019 : CollatzResearch.WordTrace tailWord_5834019 prefixEnd_5834019 2995655894462715107532341 := by
  unfold tailWord_5834019
  simp only [CollatzResearch.WordTrace]
  refine ⟨212784153851353008965153111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141856102567568672643435407 212784153851353008965153111)
  ·
    refine ⟨319176230777029513447729667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212784153851353008965153111 319176230777029513447729667)
    ·
      refine ⟨478764346165544270171594501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319176230777029513447729667 478764346165544270171594501)
      ·
        refine ⟨89768314906039550657173969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 478764346165544270171594501 89768314906039550657173969)
        ·
          refine ⟨67326236179529662992880477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89768314906039550657173969 67326236179529662992880477)
          ·
            refine ⟨25247338567323623622330179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67326236179529662992880477 25247338567323623622330179)
            ·
              refine ⟨37871007850985435433495269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25247338567323623622330179 37871007850985435433495269)
              ·
                refine ⟨7100813972059769143780363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37871007850985435433495269 7100813972059769143780363)
                ·
                  refine ⟨10651220958089653715670545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100813972059769143780363 10651220958089653715670545)
                  ·
                    refine ⟨7988415718567240286752909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10651220958089653715670545 7988415718567240286752909)
                    ·
                      refine ⟨2995655894462715107532341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988415718567240286752909 2995655894462715107532341)
                      ·
                        rfl

theorem cell23_5834019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_5834019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834019 prefixEnd_5834019 := by exact prefixLift 5834019
  have htrace : WordTrace (prefixWord ++ tailWord_5834019) baseStart_5834019 baseEnd_5834019 := by
    simpa [prefixWord, tailWord_5834019, baseEnd_5834019] using wordTrace_append hprefix tailTrace_5834019
  have hstable : (prefixWord ++ tailWord_5834019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834019).length < 2 ^ (prefixWord ++ tailWord_5834019).sum := by decide
  have hdescent : baseEnd_5834019 < baseStart_5834019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834032 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_5834032 : Nat := 118140960795 + 5834032 * 2 ^ 59
def prefixEnd_5834032 : Nat := 4983230072969 + 3 ^ 40 * 5834032 * 2
def baseEnd_5834032 : Nat := 2995662569711223556669781

theorem tailTrace_5834032 : CollatzResearch.WordTrace tailWord_5834032 prefixEnd_5834032 2995662569711223556669781 := by
  unfold tailWord_5834032
  simp only [CollatzResearch.WordTrace]
  refine ⟨106392314000152956092688175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141856418666870608123584233 106392314000152956092688175)
  ·
    refine ⟨159588471000229434139032263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106392314000152956092688175 159588471000229434139032263)
    ·
      refine ⟨239382706500344151208548395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159588471000229434139032263 239382706500344151208548395)
      ·
        refine ⟨359074059750516226812822593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239382706500344151208548395 359074059750516226812822593)
        ·
          refine ⟨269305544812887170109616945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359074059750516226812822593 269305544812887170109616945)
          ·
            refine ⟨201979158609665377582212709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269305544812887170109616945 201979158609665377582212709)
            ·
              refine ⟨37871092239312258296664883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201979158609665377582212709 37871092239312258296664883)
              ·
                refine ⟨56806638358968387444997325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37871092239312258296664883 56806638358968387444997325)
                ·
                  refine ⟨21302489384613145291873997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56806638358968387444997325 21302489384613145291873997)
                  ·
                    refine ⟨7988433519229929484452749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21302489384613145291873997 7988433519229929484452749)
                    ·
                      refine ⟨2995662569711223556669781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988433519229929484452749 2995662569711223556669781)
                      ·
                        rfl

theorem cell23_5834032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_5834032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834032 prefixEnd_5834032 := by exact prefixLift 5834032
  have htrace : WordTrace (prefixWord ++ tailWord_5834032) baseStart_5834032 baseEnd_5834032 := by
    simpa [prefixWord, tailWord_5834032, baseEnd_5834032] using wordTrace_append hprefix tailTrace_5834032
  have hstable : (prefixWord ++ tailWord_5834032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834032).length < 2 ^ (prefixWord ++ tailWord_5834032).sum := by decide
  have hdescent : baseEnd_5834032 < baseStart_5834032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834036 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_5834036 : Nat := 118140960795 + 5834036 * 2 ^ 59
def prefixEnd_5834036 : Nat := 4983230072969 + 3 ^ 40 * 5834036 * 2
def baseEnd_5834036 : Nat := 2995664623633841541019763

theorem tailTrace_5834036 : CollatzResearch.WordTrace tailWord_5834036 prefixEnd_5834036 2995664623633841541019763 := by
  unfold tailWord_5834036
  simp only [CollatzResearch.WordTrace]
  refine ⟨106392386946145710434260981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141856515928194280579014641 106392386946145710434260981)
  ·
    refine ⟨9974286276201160353211967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106392386946145710434260981 9974286276201160353211967)
    ·
      refine ⟨14961429414301740529817951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974286276201160353211967 14961429414301740529817951)
      ·
        refine ⟨22442144121452610794726927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14961429414301740529817951 22442144121452610794726927)
        ·
          refine ⟨33663216182178916192090391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22442144121452610794726927 33663216182178916192090391)
          ·
            refine ⟨50494824273268374288135587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33663216182178916192090391 50494824273268374288135587)
            ·
              refine ⟨75742236409902561432203381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50494824273268374288135587 75742236409902561432203381)
              ·
                refine ⟨7100834663428365134269067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75742236409902561432203381 7100834663428365134269067)
                ·
                  refine ⟨10651251995142547701403601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100834663428365134269067 10651251995142547701403601)
                  ·
                    refine ⟨7988438996356910776052701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10651251995142547701403601 7988438996356910776052701)
                    ·
                      refine ⟨2995664623633841541019763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988438996356910776052701 2995664623633841541019763)
                      ·
                        rfl

theorem cell23_5834036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_5834036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834036 prefixEnd_5834036 := by exact prefixLift 5834036
  have htrace : WordTrace (prefixWord ++ tailWord_5834036) baseStart_5834036 baseEnd_5834036 := by
    simpa [prefixWord, tailWord_5834036, baseEnd_5834036] using wordTrace_append hprefix tailTrace_5834036
  have hstable : (prefixWord ++ tailWord_5834036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834036).length < 2 ^ (prefixWord ++ tailWord_5834036).sum := by decide
  have hdescent : baseEnd_5834036 < baseStart_5834036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834119 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_5834119 : Nat := 118140960795 + 5834119 * 2 ^ 59
def prefixEnd_5834119 : Nat := 4983230072969 + 3 ^ 40 * 5834119 * 2
def baseEnd_5834119 : Nat := 2995707242528164716281881

theorem tailTrace_5834119 : CollatzResearch.WordTrace tailWord_5834119 prefixEnd_5834119 2995707242528164716281881 := by
  unfold tailWord_5834119
  simp only [CollatzResearch.WordTrace]
  refine ⟨212787801150990726043793411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141858534100660484029195607 212787801150990726043793411)
  ·
    refine ⟨319181701726486089065690117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212787801150990726043793411 319181701726486089065690117)
    ·
      refine ⟨59846569073716141699816897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319181701726486089065690117 59846569073716141699816897)
      ·
        refine ⟨44884926805287106274862673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59846569073716141699816897 44884926805287106274862673)
        ·
          refine ⟨33663695103965329706147005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44884926805287106274862673 33663695103965329706147005)
          ·
            refine ⟨12623885663986998639805127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33663695103965329706147005 12623885663986998639805127)
            ·
              refine ⟨18935828495980497959707691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12623885663986998639805127 18935828495980497959707691)
              ·
                refine ⟨28403742743970746939561537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18935828495980497959707691 28403742743970746939561537)
                ·
                  refine ⟨21302807057978060204671153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28403742743970746939561537 21302807057978060204671153)
                  ·
                    refine ⟨15977105293483545153503365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21302807057978060204671153 15977105293483545153503365)
                    ·
                      refine ⟨2995707242528164716281881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15977105293483545153503365 2995707242528164716281881)
                      ·
                        rfl

theorem cell23_5834119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_5834119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834119 prefixEnd_5834119 := by exact prefixLift 5834119
  have htrace : WordTrace (prefixWord ++ tailWord_5834119) baseStart_5834119 baseEnd_5834119 := by
    simpa [prefixWord, tailWord_5834119, baseEnd_5834119] using wordTrace_append hprefix tailTrace_5834119
  have hstable : (prefixWord ++ tailWord_5834119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834119).length < 2 ^ (prefixWord ++ tailWord_5834119).sum := by decide
  have hdescent : baseEnd_5834119 < baseStart_5834119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834146 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_5834146 : Nat := 118140960795 + 5834146 * 2 ^ 59
def prefixEnd_5834146 : Nat := 4983230072969 + 3 ^ 40 * 5834146 * 2
def baseEnd_5834146 : Nat := 332857900722870678960473

theorem tailTrace_5834146 : CollatzResearch.WordTrace tailWord_5834146 prefixEnd_5834146 332857900722870678960473 := by
  unfold tailWord_5834146
  simp only [CollatzResearch.WordTrace]
  refine ⟨53197196480473227413756573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141859190614595273103350861 53197196480473227413756573)
  ·
    refine ⟨19948948680177460280158715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53197196480473227413756573 19948948680177460280158715)
    ·
      refine ⟨29923423020266190420238073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19948948680177460280158715 29923423020266190420238073)
      ·
        refine ⟨22442567265199642815178555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29923423020266190420238073 22442567265199642815178555)
        ·
          refine ⟨33663850897799464222767833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22442567265199642815178555 33663850897799464222767833)
          ·
            refine ⟨25247888173349598167075875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33663850897799464222767833 25247888173349598167075875)
            ·
              refine ⟨37871832260024397250613813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25247888173349598167075875 37871832260024397250613813)
              ·
                refine ⟨3550484274377287242245045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37871832260024397250613813 3550484274377287242245045)
                ·
                  refine ⟨332857900722870678960473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550484274377287242245045 332857900722870678960473)
                  ·
                    rfl

theorem cell23_5834146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_5834146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834146 prefixEnd_5834146 := by exact prefixLift 5834146
  have htrace : WordTrace (prefixWord ++ tailWord_5834146) baseStart_5834146 baseEnd_5834146 := by
    simpa [prefixWord, tailWord_5834146, baseEnd_5834146] using wordTrace_append hprefix tailTrace_5834146
  have hstable : (prefixWord ++ tailWord_5834146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834146).length < 2 ^ (prefixWord ++ tailWord_5834146).sum := by decide
  have hdescent : baseEnd_5834146 < baseStart_5834146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834149 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_5834149 : Nat := 118140960795 + 5834149 * 2 ^ 59
def prefixEnd_5834149 : Nat := 4983230072969 + 3 ^ 40 * 5834149 * 2
def baseEnd_5834149 : Nat := 2995722646947799598906743

theorem tailTrace_5834149 : CollatzResearch.WordTrace tailWord_5834149 prefixEnd_5834149 2995722646947799598906743 := by
  unfold tailWord_5834149
  simp only [CollatzResearch.WordTrace]
  refine ⟨212788895340882041167385501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141859263560588027444923667 212788895340882041167385501)
  ·
    refine ⟨79795835752830765437769563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212788895340882041167385501 79795835752830765437769563)
    ·
      refine ⟨119693753629246148156654345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79795835752830765437769563 119693753629246148156654345)
      ·
        refine ⟨89770315221934611117490759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119693753629246148156654345 89770315221934611117490759)
        ·
          refine ⟨134655472832901916676236139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89770315221934611117490759 134655472832901916676236139)
          ·
            refine ⟨201983209249352875014354209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134655472832901916676236139 201983209249352875014354209)
            ·
              refine ⟨151487406937014656260765657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201983209249352875014354209 151487406937014656260765657)
              ·
                refine ⟨113615555202760992195574243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151487406937014656260765657 113615555202760992195574243)
                ·
                  refine ⟨170423332804141488293361365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113615555202760992195574243 170423332804141488293361365)
                  ·
                    refine ⟨3994296862597066131875657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170423332804141488293361365 3994296862597066131875657)
                    ·
                      refine ⟨2995722646947799598906743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994296862597066131875657 2995722646947799598906743)
                      ·
                        rfl

theorem cell23_5834149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_5834149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834149 prefixEnd_5834149 := by exact prefixLift 5834149
  have htrace : WordTrace (prefixWord ++ tailWord_5834149) baseStart_5834149 baseEnd_5834149 := by
    simpa [prefixWord, tailWord_5834149, baseEnd_5834149] using wordTrace_append hprefix tailTrace_5834149
  have hstable : (prefixWord ++ tailWord_5834149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834149).length < 2 ^ (prefixWord ++ tailWord_5834149).sum := by decide
  have hdescent : baseEnd_5834149 < baseStart_5834149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834157 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5834157 : Nat := 118140960795 + 5834157 * 2 ^ 59
def prefixEnd_5834157 : Nat := 4983230072969 + 3 ^ 40 * 5834157 * 2
def baseEnd_5834157 : Nat := 2995726754793035567606707

theorem tailTrace_5834157 : CollatzResearch.WordTrace tailWord_5834157 prefixEnd_5834157 2995726754793035567606707 := by
  unfold tailWord_5834157
  simp only [CollatzResearch.WordTrace]
  refine ⟨212789187124853058533676725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141859458083235372355784483 212789187124853058533676725)
  ·
    refine ⟨19948986292954974237532193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212789187124853058533676725 19948986292954974237532193)
    ·
      refine ⟨14961739719716230678149145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19948986292954974237532193 14961739719716230678149145)
      ·
        refine ⟨11221304789787173008611859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14961739719716230678149145 11221304789787173008611859)
        ·
          refine ⟨16831957184680759512917789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11221304789787173008611859 16831957184680759512917789)
          ·
            refine ⟨6311983944255284817344171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16831957184680759512917789 6311983944255284817344171)
            ·
              refine ⟨9467975916382927226016257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311983944255284817344171 9467975916382927226016257)
              ·
                refine ⟨7100981937287195419512193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9467975916382927226016257 7100981937287195419512193)
                ·
                  refine ⟨5325736452965396564634145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7100981937287195419512193 5325736452965396564634145)
                  ·
                    refine ⟨3994302339724047423475609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325736452965396564634145 3994302339724047423475609)
                    ·
                      refine ⟨2995726754793035567606707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994302339724047423475609 2995726754793035567606707)
                      ·
                        rfl

theorem cell23_5834157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5834157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834157 prefixEnd_5834157 := by exact prefixLift 5834157
  have htrace : WordTrace (prefixWord ++ tailWord_5834157) baseStart_5834157 baseEnd_5834157 := by
    simpa [prefixWord, tailWord_5834157, baseEnd_5834157] using wordTrace_append hprefix tailTrace_5834157
  have hstable : (prefixWord ++ tailWord_5834157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834157).length < 2 ^ (prefixWord ++ tailWord_5834157).sum := by decide
  have hdescent : baseEnd_5834157 < baseStart_5834157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834192 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_5834192 : Nat := 118140960795 + 5834192 * 2 ^ 59
def prefixEnd_5834192 : Nat := 4983230072969 + 3 ^ 40 * 5834192 * 2
def baseEnd_5834192 : Nat := 2995744726615942930669045

theorem tailTrace_5834192 : CollatzResearch.WordTrace tailWord_5834192 prefixEnd_5834192 2995744726615942930669045 := by
  unfold tailWord_5834192
  simp only [CollatzResearch.WordTrace]
  refine ⟨106395231839863129755600415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141860309119817506340800553 106395231839863129755600415)
  ·
    refine ⟨159592847759794694633400623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106395231839863129755600415 159592847759794694633400623)
    ·
      refine ⟨239389271639692041950100935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159592847759794694633400623 239389271639692041950100935)
      ·
        refine ⟨359083907459538062925151403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239389271639692041950100935 359083907459538062925151403)
        ·
          refine ⟨538625861189307094387727105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359083907459538062925151403 538625861189307094387727105)
          ·
            refine ⟨403969395891980320790795329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538625861189307094387727105 403969395891980320790795329)
            ·
              refine ⟨302977046918985240593096497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403969395891980320790795329 302977046918985240593096497)
              ·
                refine ⟨227232785189238930444822373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302977046918985240593096497 227232785189238930444822373)
                ·
                  refine ⟨42606147222982299458404195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227232785189238930444822373 42606147222982299458404195)
                  ·
                    refine ⟨63909220834473449187606293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42606147222982299458404195 63909220834473449187606293)
                    ·
                      refine ⟨2995744726615942930669045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63909220834473449187606293 2995744726615942930669045)
                      ·
                        rfl

theorem cell23_5834192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_5834192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834192 prefixEnd_5834192 := by exact prefixLift 5834192
  have htrace : WordTrace (prefixWord ++ tailWord_5834192) baseStart_5834192 baseEnd_5834192 := by
    simpa [prefixWord, tailWord_5834192, baseEnd_5834192] using wordTrace_append hprefix tailTrace_5834192
  have hstable : (prefixWord ++ tailWord_5834192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834192).length < 2 ^ (prefixWord ++ tailWord_5834192).sum := by decide
  have hdescent : baseEnd_5834192 < baseStart_5834192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834199 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_5834199 : Nat := 118140960795 + 5834199 * 2 ^ 59
def prefixEnd_5834199 : Nat := 4983230072969 + 3 ^ 40 * 5834199 * 2
def baseEnd_5834199 : Nat := 2995748320980524403281513

theorem tailTrace_5834199 : CollatzResearch.WordTrace tailWord_5834199 prefixEnd_5834199 2995748320980524403281513 := by
  unfold tailWord_5834199
  simp only [CollatzResearch.WordTrace]
  refine ⟨212790718990700899706705651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141860479327133933137803767 212790718990700899706705651)
  ·
    refine ⟨319186078486051349560058477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212790718990700899706705651 319186078486051349560058477)
    ·
      refine ⟨119694779432269256085021929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319186078486051349560058477 119694779432269256085021929)
      ·
        refine ⟨89771084574201942063766447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119694779432269256085021929 89771084574201942063766447)
        ·
          refine ⟨134656626861302913095649671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89771084574201942063766447 134656626861302913095649671)
          ·
            refine ⟨201984940291954369643474507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134656626861302913095649671 201984940291954369643474507)
            ·
              refine ⟨302977410437931554465211761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201984940291954369643474507 302977410437931554465211761)
              ·
                refine ⟨227233057828448665848908821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302977410437931554465211761 227233057828448665848908821)
                ·
                  refine ⟨10651549585708531211667601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227233057828448665848908821 10651549585708531211667601)
                  ·
                    refine ⟨7988662189281398408750701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10651549585708531211667601 7988662189281398408750701)
                    ·
                      refine ⟨2995748320980524403281513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988662189281398408750701 2995748320980524403281513)
                      ·
                        rfl

theorem cell23_5834199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_5834199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834199 prefixEnd_5834199 := by exact prefixLift 5834199
  have htrace : WordTrace (prefixWord ++ tailWord_5834199) baseStart_5834199 baseEnd_5834199 := by
    simpa [prefixWord, tailWord_5834199, baseEnd_5834199] using wordTrace_append hprefix tailTrace_5834199
  have hstable : (prefixWord ++ tailWord_5834199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834199).length < 2 ^ (prefixWord ++ tailWord_5834199).sum := by decide
  have hdescent : baseEnd_5834199 < baseStart_5834199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834216 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5834216 : Nat := 118140960795 + 5834216 * 2 ^ 59
def prefixEnd_5834216 : Nat := 4983230072969 + 3 ^ 40 * 5834216 * 2
def baseEnd_5834216 : Nat := 2995757050151650836768935

theorem tailTrace_5834216 : CollatzResearch.WordTrace tailWord_5834216 prefixEnd_5834216 2995757050151650836768935 := by
  unfold tailWord_5834216
  simp only [CollatzResearch.WordTrace]
  refine ⟨106395669515819655805037251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141860892687759541073383001 106395669515819655805037251)
  ·
    refine ⟨159593504273729483707555877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106395669515819655805037251 159593504273729483707555877)
    ·
      refine ⟨29923782051324278195166727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159593504273729483707555877 29923782051324278195166727)
      ·
        refine ⟨44885673076986417292750091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29923782051324278195166727 44885673076986417292750091)
        ·
          refine ⟨67328509615479625939125137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44885673076986417292750091 67328509615479625939125137)
          ·
            refine ⟨50496382211609719454343853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67328509615479625939125137 50496382211609719454343853)
            ·
              refine ⟨18936143329353644795378945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50496382211609719454343853 18936143329353644795378945)
              ·
                refine ⟨14202107497015233596534209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18936143329353644795378945 14202107497015233596534209)
                ·
                  refine ⟨10651580622761425197400657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14202107497015233596534209 10651580622761425197400657)
                  ·
                    refine ⟨7988685467071068898050493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10651580622761425197400657 7988685467071068898050493)
                    ·
                      refine ⟨2995757050151650836768935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988685467071068898050493 2995757050151650836768935)
                      ·
                        rfl

theorem cell23_5834216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5834216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834216 prefixEnd_5834216 := by exact prefixLift 5834216
  have htrace : WordTrace (prefixWord ++ tailWord_5834216) baseStart_5834216 baseEnd_5834216 := by
    simpa [prefixWord, tailWord_5834216, baseEnd_5834216] using wordTrace_append hprefix tailTrace_5834216
  have hstable : (prefixWord ++ tailWord_5834216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834216).length < 2 ^ (prefixWord ++ tailWord_5834216).sum := by decide
  have hdescent : baseEnd_5834216 < baseStart_5834216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834236 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 6]
def baseStart_5834236 : Nat := 118140960795 + 5834236 * 2 ^ 59
def prefixEnd_5834236 : Nat := 4983230072969 + 3 ^ 40 * 5834236 * 2
def baseEnd_5834236 : Nat := 332863035529415639835427

theorem tailTrace_5834236 : CollatzResearch.WordTrace tailWord_5834236 prefixEnd_5834236 332863035529415639835427 := by
  unfold tailWord_5834236
  simp only [CollatzResearch.WordTrace]
  refine ⟨106396034245783427512901281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141861378994377903350535041 106396034245783427512901281)
  ·
    refine ⟨79797025684337570634675961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106396034245783427512901281 79797025684337570634675961)
    ·
      refine ⟨59847769263253177976006971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79797025684337570634675961 59847769263253177976006971)
      ·
        refine ⟨89771653894879766964010457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59847769263253177976006971 89771653894879766964010457)
        ·
          refine ⟨67328740421159825223007843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89771653894879766964010457 67328740421159825223007843)
          ·
            refine ⟨100993110631739737834511765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67328740421159825223007843 100993110631739737834511765)
            ·
              refine ⟨4734052060862800210992739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100993110631739737834511765 4734052060862800210992739)
              ·
                refine ⟨7101078091294200316489109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734052060862800210992739 7101078091294200316489109)
                ·
                  refine ⟨332863035529415639835427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7101078091294200316489109 332863035529415639835427)
                  ·
                    rfl

theorem cell23_5834236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_5834236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834236 prefixEnd_5834236 := by exact prefixLift 5834236
  have htrace : WordTrace (prefixWord ++ tailWord_5834236) baseStart_5834236 baseEnd_5834236 := by
    simpa [prefixWord, tailWord_5834236, baseEnd_5834236] using wordTrace_append hprefix tailTrace_5834236
  have hstable : (prefixWord ++ tailWord_5834236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834236).length < 2 ^ (prefixWord ++ tailWord_5834236).sum := by decide
  have hdescent : baseEnd_5834236 < baseStart_5834236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834249 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_5834249 : Nat := 118140960795 + 5834249 * 2 ^ 59
def prefixEnd_5834249 : Nat := 4983230072969 + 3 ^ 40 * 5834249 * 2
def baseEnd_5834249 : Nat := 998591331671083069218761

theorem tailTrace_5834249 : CollatzResearch.WordTrace tailWord_5834249 prefixEnd_5834249 998591331671083069218761 := by
  unfold tailWord_5834249
  simp only [CollatzResearch.WordTrace]
  refine ⟨212792542640519758246025801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141861695093679838830683867 212792542640519758246025801)
  ·
    refine ⟨159594406980389818684519351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212792542640519758246025801 159594406980389818684519351)
    ·
      refine ⟨239391610470584728026779027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159594406980389818684519351 239391610470584728026779027)
      ·
        refine ⟨359087415705877092040168541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239391610470584728026779027 359087415705877092040168541)
        ·
          refine ⟨134657780889703909515063203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359087415705877092040168541 134657780889703909515063203)
          ·
            refine ⟨201986671334555864272594805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134657780889703909515063203 201986671334555864272594805)
            ·
              refine ⟨18936250437614612275555763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201986671334555864272594805 18936250437614612275555763)
              ·
                refine ⟨28404375656421918413333645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18936250437614612275555763 28404375656421918413333645)
                ·
                  refine ⟨10651640871158219405000117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28404375656421918413333645 10651640871158219405000117)
                  ·
                    refine ⟨998591331671083069218761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10651640871158219405000117 998591331671083069218761)
                    ·
                      rfl

theorem cell23_5834249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_5834249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834249 prefixEnd_5834249 := by exact prefixLift 5834249
  have htrace : WordTrace (prefixWord ++ tailWord_5834249) baseStart_5834249 baseEnd_5834249 := by
    simpa [prefixWord, tailWord_5834249, baseEnd_5834249] using wordTrace_append hprefix tailTrace_5834249
  have hstable : (prefixWord ++ tailWord_5834249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834249).length < 2 ^ (prefixWord ++ tailWord_5834249).sum := by decide
  have hdescent : baseEnd_5834249 < baseStart_5834249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834273 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5834273 : Nat := 118140960795 + 5834273 * 2 ^ 59
def prefixEnd_5834273 : Nat := 4983230072969 + 3 ^ 40 * 5834273 * 2
def baseEnd_5834273 : Nat := 2995786318548957113756173

theorem tailTrace_5834273 : CollatzResearch.WordTrace tailWord_5834273 prefixEnd_5834273 2995786318548957113756173 := by
  unfold tailWord_5834273
  simp only [CollatzResearch.WordTrace]
  refine ⟨212793417992432810344899473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141862278661621873563266315 212793417992432810344899473)
  ·
    refine ⟨159595063494324607758674605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212793417992432810344899473 159595063494324607758674605)
    ·
      refine ⟨59848148810371727909502977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159595063494324607758674605 59848148810371727909502977)
      ·
        refine ⟨44886111607778795932127233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59848148810371727909502977 44886111607778795932127233)
        ·
          refine ⟨33664583705834096949095425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44886111607778795932127233 33664583705834096949095425)
          ·
            refine ⟨25248437779375572711821569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33664583705834096949095425 25248437779375572711821569)
            ·
              refine ⟨18936328334531679533866177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25248437779375572711821569 18936328334531679533866177)
              ·
                refine ⟨14202246250898759650399633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18936328334531679533866177 14202246250898759650399633)
                ·
                  refine ⟨10651684688174069737799725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14202246250898759650399633 10651684688174069737799725)
                  ·
                    refine ⟨3994381758065276151674897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10651684688174069737799725 3994381758065276151674897)
                    ·
                      refine ⟨2995786318548957113756173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994381758065276151674897 2995786318548957113756173)
                      ·
                        rfl

theorem cell23_5834273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5834273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834273 prefixEnd_5834273 := by exact prefixLift 5834273
  have htrace : WordTrace (prefixWord ++ tailWord_5834273) baseStart_5834273 baseEnd_5834273 := by
    simpa [prefixWord, tailWord_5834273, baseEnd_5834273] using wordTrace_append hprefix tailTrace_5834273
  have hstable : (prefixWord ++ tailWord_5834273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834273).length < 2 ^ (prefixWord ++ tailWord_5834273).sum := by decide
  have hdescent : baseEnd_5834273 < baseStart_5834273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834289 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_5834289 : Nat := 118140960795 + 5834289 * 2 ^ 59
def prefixEnd_5834289 : Nat := 4983230072969 + 3 ^ 40 * 5834289 * 2
def baseEnd_5834289 : Nat := 2995794534239429051156099

theorem tailTrace_5834289 : CollatzResearch.WordTrace tailWord_5834289 prefixEnd_5834289 2995794534239429051156099 := by
  unfold tailWord_5834289
  simp only [CollatzResearch.WordTrace]
  refine ⟨212794001560374845077481921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141862667706916563384987947 212794001560374845077481921)
  ·
    refine ⟨159595501170281133808111441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212794001560374845077481921 159595501170281133808111441)
    ·
      refine ⟨119696625877710850356083581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159595501170281133808111441 119696625877710850356083581)
      ·
        refine ⟨44886234704141568883531343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119696625877710850356083581 44886234704141568883531343)
        ·
          refine ⟨67329352056212353325297015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44886234704141568883531343 67329352056212353325297015)
          ·
            refine ⟨100994028084318529987945523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67329352056212353325297015 100994028084318529987945523)
            ·
              refine ⟨151491042126477794981918285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100994028084318529987945523 151491042126477794981918285)
              ·
                refine ⟨56809140797429173118219357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151491042126477794981918285 56809140797429173118219357)
                ·
                  refine ⟨21303427799035939919332259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56809140797429173118219357 21303427799035939919332259)
                  ·
                    refine ⟨31955141698553909878998389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21303427799035939919332259 31955141698553909878998389)
                    ·
                      refine ⟨2995794534239429051156099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31955141698553909878998389 2995794534239429051156099)
                      ·
                        rfl

theorem cell23_5834289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_5834289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834289 prefixEnd_5834289 := by exact prefixLift 5834289
  have htrace : WordTrace (prefixWord ++ tailWord_5834289) baseStart_5834289 baseEnd_5834289 := by
    simpa [prefixWord, tailWord_5834289, baseEnd_5834289] using wordTrace_append hprefix tailTrace_5834289
  have hstable : (prefixWord ++ tailWord_5834289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834289).length < 2 ^ (prefixWord ++ tailWord_5834289).sum := by decide
  have hdescent : baseEnd_5834289 < baseStart_5834289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834296 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_5834296 : Nat := 118140960795 + 5834296 * 2 ^ 59
def prefixEnd_5834296 : Nat := 4983230072969 + 3 ^ 40 * 5834296 * 2
def baseEnd_5834296 : Nat := 998599376201336841256189

theorem tailTrace_5834296 : CollatzResearch.WordTrace tailWord_5834296 prefixEnd_5834296 998599376201336841256189 := by
  unfold tailWord_5834296
  simp only [CollatzResearch.WordTrace]
  refine ⟨106397128435674742636493371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141862837914232990181991161 106397128435674742636493371)
  ·
    refine ⟨159595692653512113954740057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106397128435674742636493371 159595692653512113954740057)
    ·
      refine ⟨119696769490134085466055043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159595692653512113954740057 119696769490134085466055043)
      ·
        refine ⟨179545154235201128199082565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119696769490134085466055043 179545154235201128199082565)
        ·
          refine ⟨33664716419100211537327981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179545154235201128199082565 33664716419100211537327981)
          ·
            refine ⟨12624268657162579326497993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33664716419100211537327981 12624268657162579326497993)
            ·
              refine ⟨9468201492871934494873495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624268657162579326497993 9468201492871934494873495)
              ·
                refine ⟨14202302239307901742310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468201492871934494873495 14202302239307901742310243)
                ·
                  refine ⟨21303453358961852613465365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14202302239307901742310243 21303453358961852613465365)
                  ·
                    refine ⟨998599376201336841256189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21303453358961852613465365 998599376201336841256189)
                    ·
                      rfl

theorem cell23_5834296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_5834296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834296 prefixEnd_5834296 := by exact prefixLift 5834296
  have htrace : WordTrace (prefixWord ++ tailWord_5834296) baseStart_5834296 baseEnd_5834296 := by
    simpa [prefixWord, tailWord_5834296, baseEnd_5834296] using wordTrace_append hprefix tailTrace_5834296
  have hstable : (prefixWord ++ tailWord_5834296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834296).length < 2 ^ (prefixWord ++ tailWord_5834296).sum := by decide
  have hdescent : baseEnd_5834296 < baseStart_5834296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834303 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 5, 2, 2]
def baseStart_5834303 : Nat := 118140960795 + 5834303 * 2 ^ 59
def prefixEnd_5834303 : Nat := 4983230072969 + 3 ^ 40 * 5834303 * 2
def baseEnd_5834303 : Nat := 2995801722968591996381035

theorem tailTrace_5834303 : CollatzResearch.WordTrace tailWord_5834303 prefixEnd_5834303 2995801722968591996381035 := by
  unfold tailWord_5834303
  simp only [CollatzResearch.WordTrace]
  refine ⟨212794512182324125468491563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141863008121549416978994375 212794512182324125468491563)
  ·
    refine ⟨319191768273486188202737345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212794512182324125468491563 319191768273486188202737345)
    ·
      refine ⟨239393826205114641152053009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319191768273486188202737345 239393826205114641152053009)
      ·
        refine ⟨179545369653835980864039757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239393826205114641152053009 179545369653835980864039757)
        ·
          refine ⟨67329513620188492824014909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179545369653835980864039757 67329513620188492824014909)
          ·
            refine ⟨25248567607570684809005591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67329513620188492824014909 25248567607570684809005591)
            ·
              refine ⟨37872851411356027213508387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25248567607570684809005591 37872851411356027213508387)
              ·
                refine ⟨56809277117034040820262581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37872851411356027213508387 56809277117034040820262581)
                ·
                  refine ⟨5325869729721941326899617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56809277117034040820262581 5325869729721941326899617)
                  ·
                    refine ⟨3994402297291455995174713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325869729721941326899617 3994402297291455995174713)
                    ·
                      refine ⟨2995801722968591996381035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994402297291455995174713 2995801722968591996381035)
                      ·
                        rfl

theorem cell23_5834303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_5834303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834303 prefixEnd_5834303 := by exact prefixLift 5834303
  have htrace : WordTrace (prefixWord ++ tailWord_5834303) baseStart_5834303 baseEnd_5834303 := by
    simpa [prefixWord, tailWord_5834303, baseEnd_5834303] using wordTrace_append hprefix tailTrace_5834303
  have hstable : (prefixWord ++ tailWord_5834303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834303).length < 2 ^ (prefixWord ++ tailWord_5834303).sum := by decide
  have hdescent : baseEnd_5834303 < baseStart_5834303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834316 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5834316 : Nat := 118140960795 + 5834316 * 2 ^ 59
def prefixEnd_5834316 : Nat := 4983230072969 + 3 ^ 40 * 5834316 * 2
def baseEnd_5834316 : Nat := 2995808398217100445518475

theorem tailTrace_5834316 : CollatzResearch.WordTrace tailWord_5834316 prefixEnd_5834316 2995808398217100445518475 := by
  unfold tailWord_5834316
  simp only [CollatzResearch.WordTrace]
  refine ⟨106397493165638514344357401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141863324220851352459143201 106397493165638514344357401)
  ·
    refine ⟨79798119874228885758268051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106397493165638514344357401 79798119874228885758268051)
    ·
      refine ⟨119697179811343328637402077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79798119874228885758268051 119697179811343328637402077)
      ·
        refine ⟨44886442429253748239025779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119697179811343328637402077 44886442429253748239025779)
        ·
          refine ⟨67329663643880622358538669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44886442429253748239025779 67329663643880622358538669)
          ·
            refine ⟨25248623866455233384452001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67329663643880622358538669 25248623866455233384452001)
            ·
              refine ⟨18936467899841425038339001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25248623866455233384452001 18936467899841425038339001)
              ·
                refine ⟨14202350924881068778754251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18936467899841425038339001 14202350924881068778754251)
                ·
                  refine ⟨21303526387321603168131377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14202350924881068778754251 21303526387321603168131377)
                  ·
                    refine ⟨15977644790491202376098533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21303526387321603168131377 15977644790491202376098533)
                    ·
                      refine ⟨2995808398217100445518475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15977644790491202376098533 2995808398217100445518475)
                      ·
                        rfl

theorem cell23_5834316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5834316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834316 prefixEnd_5834316 := by exact prefixLift 5834316
  have htrace : WordTrace (prefixWord ++ tailWord_5834316) baseStart_5834316 baseEnd_5834316 := by
    simpa [prefixWord, tailWord_5834316, baseEnd_5834316] using wordTrace_append hprefix tailTrace_5834316
  have hstable : (prefixWord ++ tailWord_5834316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834316).length < 2 ^ (prefixWord ++ tailWord_5834316).sum := by decide
  have hdescent : baseEnd_5834316 < baseStart_5834316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834317 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_5834317 : Nat := 118140960795 + 5834317 * 2 ^ 59
def prefixEnd_5834317 : Nat := 4983230072969 + 3 ^ 40 * 5834317 * 2
def baseEnd_5834317 : Nat := 998602970565918313868657

theorem tailTrace_5834317 : CollatzResearch.WordTrace tailWord_5834317 prefixEnd_5834317 998602970565918313868657 := by
  unfold tailWord_5834317
  simp only [CollatzResearch.WordTrace]
  refine ⟨212795022804273405859501205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141863348536182270573000803 212795022804273405859501205)
  ·
    refine ⟨9974766693950315899664119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212795022804273405859501205 9974766693950315899664119)
    ·
      refine ⟨14962150040925473849496179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974766693950315899664119 14962150040925473849496179)
      ·
        refine ⟨22443225061388210774244269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14962150040925473849496179 22443225061388210774244269)
        ·
          refine ⟨8416209398020579040341601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22443225061388210774244269 8416209398020579040341601)
          ·
            refine ⟨6312157048515434280256201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416209398020579040341601 6312157048515434280256201)
            ·
              refine ⟨4734117786386575710192151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6312157048515434280256201 4734117786386575710192151)
              ·
                refine ⟨7101176679579863565288227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734117786386575710192151 7101176679579863565288227)
                ·
                  refine ⟨10651765019369795347932341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7101176679579863565288227 10651765019369795347932341)
                  ·
                    refine ⟨998602970565918313868657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10651765019369795347932341 998602970565918313868657)
                    ·
                      rfl

theorem cell23_5834317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_5834317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834317 prefixEnd_5834317 := by exact prefixLift 5834317
  have htrace : WordTrace (prefixWord ++ tailWord_5834317) baseStart_5834317 baseEnd_5834317 := by
    simpa [prefixWord, tailWord_5834317, baseEnd_5834317] using wordTrace_append hprefix tailTrace_5834317
  have hstable : (prefixWord ++ tailWord_5834317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834317).length < 2 ^ (prefixWord ++ tailWord_5834317).sum := by decide
  have hdescent : baseEnd_5834317 < baseStart_5834317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834350 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5834350 : Nat := 118140960795 + 5834350 * 2 ^ 59
def prefixEnd_5834350 : Nat := 4983230072969 + 3 ^ 40 * 5834350 * 2
def baseEnd_5834350 : Nat := 2995825856559353312493319

theorem tailTrace_5834350 : CollatzResearch.WordTrace tailWord_5834350 prefixEnd_5834350 2995825856559353312493319 := by
  unfold tailWord_5834350
  simp only [CollatzResearch.WordTrace]
  refine ⟨26599528301644231561931563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141864150942102568330301669 26599528301644231561931563)
  ·
    refine ⟨39899292452466347342897345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26599528301644231561931563 39899292452466347342897345)
    ·
      refine ⟨29924469339349760507173009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39899292452466347342897345 29924469339349760507173009)
      ·
        refine ⟨22443352004512320380379757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29924469339349760507173009 22443352004512320380379757)
        ·
          refine ⟨8416257001692120142642409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22443352004512320380379757 8416257001692120142642409)
          ·
            refine ⟨6312192751269090106981807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416257001692120142642409 6312192751269090106981807)
            ·
              refine ⟨9468289126903635160472711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312192751269090106981807 9468289126903635160472711)
              ·
                refine ⟨14202433690355452740709067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468289126903635160472711 14202433690355452740709067)
                ·
                  refine ⟨21303650535533179111063601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14202433690355452740709067 21303650535533179111063601)
                  ·
                    refine ⟨15977737901649884333297701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21303650535533179111063601 15977737901649884333297701)
                    ·
                      refine ⟨2995825856559353312493319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15977737901649884333297701 2995825856559353312493319)
                      ·
                        rfl

theorem cell23_5834350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5834350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834350 prefixEnd_5834350 := by exact prefixLift 5834350
  have htrace : WordTrace (prefixWord ++ tailWord_5834350) baseStart_5834350 baseEnd_5834350 := by
    simpa [prefixWord, tailWord_5834350, baseEnd_5834350] using wordTrace_append hprefix tailTrace_5834350
  have hstable : (prefixWord ++ tailWord_5834350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834350).length < 2 ^ (prefixWord ++ tailWord_5834350).sum := by decide
  have hdescent : baseEnd_5834350 < baseStart_5834350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834353 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_5834353 : Nat := 118140960795 + 5834353 * 2 ^ 59
def prefixEnd_5834353 : Nat := 4983230072969 + 3 ^ 40 * 5834353 * 2
def baseEnd_5834353 : Nat := 2995827397001316800755805

theorem tailTrace_5834353 : CollatzResearch.WordTrace tailWord_5834353 prefixEnd_5834353 2995827397001316800755805 := by
  unfold tailWord_5834353
  simp only [CollatzResearch.WordTrace]
  refine ⟨212796335832142984007811713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141864223888095322671874475 212796335832142984007811713)
  ·
    refine ⟨159597251874107238005858785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212796335832142984007811713 159597251874107238005858785)
    ·
      refine ⟨119697938905580428504394089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159597251874107238005858785 119697938905580428504394089)
      ·
        refine ⟨89773454179185321378295567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119697938905580428504394089 89773454179185321378295567)
        ·
          refine ⟨134660181268777982067443351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89773454179185321378295567 134660181268777982067443351)
          ·
            refine ⟨201990271903166973101165027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134660181268777982067443351 201990271903166973101165027)
            ·
              refine ⟨302985407854750459651747541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201990271903166973101165027 302985407854750459651747541)
              ·
                refine ⟨7101220496595713898087833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 302985407854750459651747541 7101220496595713898087833)
                ·
                  refine ⟨5325915372446785423565875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7101220496595713898087833 5325915372446785423565875)
                  ·
                    refine ⟨7988873058670178135348813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5325915372446785423565875 7988873058670178135348813)
                    ·
                      refine ⟨2995827397001316800755805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7988873058670178135348813 2995827397001316800755805)
                      ·
                        rfl

theorem cell23_5834353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_5834353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834353 prefixEnd_5834353 := by exact prefixLift 5834353
  have htrace : WordTrace (prefixWord ++ tailWord_5834353) baseStart_5834353 baseEnd_5834353 := by
    simpa [prefixWord, tailWord_5834353, baseEnd_5834353] using wordTrace_append hprefix tailTrace_5834353
  have hstable : (prefixWord ++ tailWord_5834353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834353).length < 2 ^ (prefixWord ++ tailWord_5834353).sum := by decide
  have hdescent : baseEnd_5834353 < baseStart_5834353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834409 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_5834409 : Nat := 118140960795 + 5834409 * 2 ^ 59
def prefixEnd_5834409 : Nat := 4983230072969 + 3 ^ 40 * 5834409 * 2
def baseEnd_5834409 : Nat := 2995856151917968581655547

theorem tailTrace_5834409 : CollatzResearch.WordTrace tailWord_5834409 prefixEnd_5834409 2995856151917968581655547 := by
  unfold tailWord_5834409
  simp only [CollatzResearch.WordTrace]
  refine ⟨212798378319940105571850281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141865585546626737047900187 212798378319940105571850281)
  ·
    refine ⟨159598783739955079178887711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212798378319940105571850281 159598783739955079178887711)
    ·
      refine ⟨239398175609932618768331567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159598783739955079178887711 239398175609932618768331567)
      ·
        refine ⟨359097263414898928152497351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239398175609932618768331567 359097263414898928152497351)
        ·
          refine ⟨538645895122348392228746027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359097263414898928152497351 538645895122348392228746027)
          ·
            refine ⟨807968842683522588343119041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538645895122348392228746027 807968842683522588343119041)
            ·
              refine ⟨605976632012641941257339281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807968842683522588343119041 605976632012641941257339281)
              ·
                refine ⟨454482474009481455943004461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605976632012641941257339281 454482474009481455943004461)
                ·
                  refine ⟨170430927753555545978626673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454482474009481455943004461 170430927753555545978626673)
                  ·
                    refine ⟨127823195815166659483970005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170430927753555545978626673 127823195815166659483970005)
                    ·
                      refine ⟨2995856151917968581655547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127823195815166659483970005 2995856151917968581655547)
                      ·
                        rfl

theorem cell23_5834409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_5834409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834409 prefixEnd_5834409 := by exact prefixLift 5834409
  have htrace : WordTrace (prefixWord ++ tailWord_5834409) baseStart_5834409 baseEnd_5834409 := by
    simpa [prefixWord, tailWord_5834409, baseEnd_5834409] using wordTrace_append hprefix tailTrace_5834409
  have hstable : (prefixWord ++ tailWord_5834409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834409).length < 2 ^ (prefixWord ++ tailWord_5834409).sum := by decide
  have hdescent : baseEnd_5834409 < baseStart_5834409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834444 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5834444 : Nat := 118140960795 + 5834444 * 2 ^ 59
def prefixEnd_5834444 : Nat := 4983230072969 + 3 ^ 40 * 5834444 * 2
def baseEnd_5834444 : Nat := 2995874123740875944717887

theorem tailTrace_5834444 : CollatzResearch.WordTrace tailWord_5834444 prefixEnd_5834444 2995874123740875944717887 := by
  unfold tailWord_5834444
  simp only [CollatzResearch.WordTrace]
  refine ⟨106399827437406653274687193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141866436583208871032916257 106399827437406653274687193)
  ·
    refine ⟨79799870578054989956015395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106399827437406653274687193 79799870578054989956015395)
    ·
      refine ⟨119699805867082484934023093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79799870578054989956015395 119699805867082484934023093)
      ·
        refine ⟨11221856800038982962564665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119699805867082484934023093 11221856800038982962564665)
        ·
          refine ⟨8416392600029237221923499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11221856800038982962564665 8416392600029237221923499)
          ·
            refine ⟨12624588900043855832885249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416392600029237221923499 12624588900043855832885249)
            ·
              refine ⟨9468441675032891874663937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624588900043855832885249 9468441675032891874663937)
              ·
                refine ⟨7101331256274668905997953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9468441675032891874663937 7101331256274668905997953)
                ·
                  refine ⟨5325998442206001679498465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7101331256274668905997953 5325998442206001679498465)
                  ·
                    refine ⟨3994498831654501259623849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325998442206001679498465 3994498831654501259623849)
                    ·
                      refine ⟨2995874123740875944717887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994498831654501259623849 2995874123740875944717887)
                      ·
                        rfl

theorem cell23_5834444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5834444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834444 prefixEnd_5834444 := by exact prefixLift 5834444
  have htrace : WordTrace (prefixWord ++ tailWord_5834444) baseStart_5834444 baseEnd_5834444 := by
    simpa [prefixWord, tailWord_5834444, baseEnd_5834444] using wordTrace_append hprefix tailTrace_5834444
  have hstable : (prefixWord ++ tailWord_5834444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834444).length < 2 ^ (prefixWord ++ tailWord_5834444).sum := by decide
  have hdescent : baseEnd_5834444 < baseStart_5834444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834450 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_5834450 : Nat := 118140960795 + 5834450 * 2 ^ 59
def prefixEnd_5834450 : Nat := 4983230072969 + 3 ^ 40 * 5834450 * 2
def baseEnd_5834450 : Nat := 332875244958311435693651

theorem tailTrace_5834450 : CollatzResearch.WordTrace tailWord_5834450 prefixEnd_5834450 332875244958311435693651 := by
  unfold tailWord_5834450
  simp only [CollatzResearch.WordTrace]
  refine ⟨53199968428197892393523201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141866582475194379716061869 53199968428197892393523201)
  ·
    refine ⟨39899976321148419295142401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53199968428197892393523201 39899976321148419295142401)
    ·
      refine ⟨29924982240861314471356801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39899976321148419295142401 29924982240861314471356801)
      ·
        refine ⟨22443736680645985853517601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29924982240861314471356801 22443736680645985853517601)
        ·
          refine ⟨16832802510484489390138201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22443736680645985853517601 16832802510484489390138201)
          ·
            refine ⟨12624601882863367042603651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16832802510484489390138201 12624601882863367042603651)
            ·
              refine ⟨18936902824295050563905477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12624601882863367042603651 18936902824295050563905477)
              ·
                refine ⟨3550669279555321980732277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18936902824295050563905477 3550669279555321980732277)
                ·
                  refine ⟨332875244958311435693651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550669279555321980732277 332875244958311435693651)
                  ·
                    rfl

theorem cell23_5834450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_5834450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834450 prefixEnd_5834450 := by exact prefixLift 5834450
  have htrace : WordTrace (prefixWord ++ tailWord_5834450) baseStart_5834450 baseEnd_5834450 := by
    simpa [prefixWord, tailWord_5834450, baseEnd_5834450] using wordTrace_append hprefix tailTrace_5834450
  have hstable : (prefixWord ++ tailWord_5834450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834450).length < 2 ^ (prefixWord ++ tailWord_5834450).sum := by decide
  have hdescent : baseEnd_5834450 < baseStart_5834450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834456 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_5834456 : Nat := 118140960795 + 5834456 * 2 ^ 59
def prefixEnd_5834456 : Nat := 4983230072969 + 3 ^ 40 * 5834456 * 2
def baseEnd_5834456 : Nat := 2995880285508729897767831

theorem tailTrace_5834456 : CollatzResearch.WordTrace tailWord_5834456 prefixEnd_5834456 2995880285508729897767831 := by
  unfold tailWord_5834456
  simp only [CollatzResearch.WordTrace]
  refine ⟨106400046275384916299405611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141866728367179888399207481 106400046275384916299405611)
  ·
    refine ⟨159600069413077374449108417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106400046275384916299405611 159600069413077374449108417)
    ·
      refine ⟨119700052059808030836831313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159600069413077374449108417 119700052059808030836831313)
      ·
        refine ⟨89775039044856023127623485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119700052059808030836831313 89775039044856023127623485)
        ·
          refine ⟨33665639641821008672858807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89775039044856023127623485 33665639641821008672858807)
          ·
            refine ⟨50498459462731513009288211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33665639641821008672858807 50498459462731513009288211)
            ·
              refine ⟨75747689194097269513932317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50498459462731513009288211 75747689194097269513932317)
              ·
                refine ⟨28405383447786476067724619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75747689194097269513932317 28405383447786476067724619)
                ·
                  refine ⟨42608075171679714101586929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28405383447786476067724619 42608075171679714101586929)
                  ·
                    refine ⟨31956056378759785576190197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42608075171679714101586929 31956056378759785576190197)
                    ·
                      refine ⟨2995880285508729897767831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31956056378759785576190197 2995880285508729897767831)
                      ·
                        rfl

theorem cell23_5834456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_5834456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834456 prefixEnd_5834456 := by exact prefixLift 5834456
  have htrace : WordTrace (prefixWord ++ tailWord_5834456) baseStart_5834456 baseEnd_5834456 := by
    simpa [prefixWord, tailWord_5834456, baseEnd_5834456] using wordTrace_append hprefix tailTrace_5834456
  have hstable : (prefixWord ++ tailWord_5834456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834456).length < 2 ^ (prefixWord ++ tailWord_5834456).sum := by decide
  have hdescent : baseEnd_5834456 < baseStart_5834456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834483 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4]
def baseStart_5834483 : Nat := 118140960795 + 5834483 * 2 ^ 59
def prefixEnd_5834483 : Nat := 4983230072969 + 3 ^ 40 * 5834483 * 2
def baseEnd_5834483 : Nat := 2995894149486401292130207

theorem tailTrace_5834483 : CollatzResearch.WordTrace tailWord_5834483 prefixEnd_5834483 2995894149486401292130207 := by
  unfold tailWord_5834483
  simp only [CollatzResearch.WordTrace]
  refine ⟨212801077321672016210044103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141867384881114677473362735 212801077321672016210044103)
  ·
    refine ⟨319201615982508024315066155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212801077321672016210044103 319201615982508024315066155)
    ·
      refine ⟨478802423973762036472599233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319201615982508024315066155 478802423973762036472599233)
      ·
        refine ⟨359101817980321527354449425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478802423973762036472599233 359101817980321527354449425)
        ·
          refine ⟨269326363485241145515837069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359101817980321527354449425 269326363485241145515837069)
          ·
            refine ⟨100997386306965429568438901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269326363485241145515837069 100997386306965429568438901)
            ·
              refine ⟨9468504966278009022041147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100997386306965429568438901 9468504966278009022041147)
              ·
                refine ⟨14202757449417013533061721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468504966278009022041147 14202757449417013533061721)
                ·
                  refine ⟨10652068087062760149796291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14202757449417013533061721 10652068087062760149796291)
                  ·
                    refine ⟨15978102130594140224694437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10652068087062760149796291 15978102130594140224694437)
                    ·
                      refine ⟨2995894149486401292130207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15978102130594140224694437 2995894149486401292130207)
                      ·
                        rfl

theorem cell23_5834483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_5834483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834483 prefixEnd_5834483 := by exact prefixLift 5834483
  have htrace : WordTrace (prefixWord ++ tailWord_5834483) baseStart_5834483 baseEnd_5834483 := by
    simpa [prefixWord, tailWord_5834483, baseEnd_5834483] using wordTrace_append hprefix tailTrace_5834483
  have hstable : (prefixWord ++ tailWord_5834483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834483).length < 2 ^ (prefixWord ++ tailWord_5834483).sum := by decide
  have hdescent : baseEnd_5834483 < baseStart_5834483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834484 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5834484 : Nat := 118140960795 + 5834484 * 2 ^ 59
def prefixEnd_5834484 : Nat := 4983230072969 + 3 ^ 40 * 5834484 * 2
def baseEnd_5834484 : Nat := 332877184774117309801967

theorem tailTrace_5834484 : CollatzResearch.WordTrace tailWord_5834484 prefixEnd_5834484 332877184774117309801967 := by
  unfold tailWord_5834484
  simp only [CollatzResearch.WordTrace]
  refine ⟨106400556897334196690415253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141867409196445595587220337 106400556897334196690415253)
  ·
    refine ⟨4987526104562540469863215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106400556897334196690415253 4987526104562540469863215)
    ·
      refine ⟨7481289156843810704794823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4987526104562540469863215 7481289156843810704794823)
      ·
        refine ⟨11221933735265716057192235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7481289156843810704794823 11221933735265716057192235)
        ·
          refine ⟨16832900602898574085788353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11221933735265716057192235 16832900602898574085788353)
          ·
            refine ⟨12624675452173930564341265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16832900602898574085788353 12624675452173930564341265)
            ·
              refine ⟨9468506589130447923255949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624675452173930564341265 9468506589130447923255949)
              ·
                refine ⟨3550689970923917971220981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9468506589130447923255949 3550689970923917971220981)
                ·
                  refine ⟨332877184774117309801967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550689970923917971220981 332877184774117309801967)
                  ·
                    rfl

theorem cell23_5834484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5834484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834484 prefixEnd_5834484 := by exact prefixLift 5834484
  have htrace : WordTrace (prefixWord ++ tailWord_5834484) baseStart_5834484 baseEnd_5834484 := by
    simpa [prefixWord, tailWord_5834484, baseEnd_5834484] using wordTrace_append hprefix tailTrace_5834484
  have hstable : (prefixWord ++ tailWord_5834484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834484).length < 2 ^ (prefixWord ++ tailWord_5834484).sum := by decide
  have hdescent : baseEnd_5834484 < baseStart_5834484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834500 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5834500 : Nat := 118140960795 + 5834500 * 2 ^ 59
def prefixEnd_5834500 : Nat := 4983230072969 + 3 ^ 40 * 5834500 * 2
def baseEnd_5834500 : Nat := 2995902878657527725617629

theorem tailTrace_5834500 : CollatzResearch.WordTrace tailWord_5834500 prefixEnd_5834500 2995902878657527725617629 := by
  unfold tailWord_5834500
  simp only [CollatzResearch.WordTrace]
  refine ⟨106400848681305214056706477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141867798241740285408941969 106400848681305214056706477)
  ·
    refine ⟨39900318255489455271264929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106400848681305214056706477 39900318255489455271264929)
    ·
      refine ⟨29925238691617091453448697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39900318255489455271264929 29925238691617091453448697)
      ·
        refine ⟨22443929018712818590086523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29925238691617091453448697 22443929018712818590086523)
        ·
          refine ⟨33665893528069227885129785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22443929018712818590086523 33665893528069227885129785)
          ·
            refine ⟨25249420146051920913847339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33665893528069227885129785 25249420146051920913847339)
            ·
              refine ⟨37874130219077881370771009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25249420146051920913847339 37874130219077881370771009)
              ·
                refine ⟨28405597664308411028078257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37874130219077881370771009 28405597664308411028078257)
                ·
                  refine ⟨21304198248231308271058693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28405597664308411028078257 21304198248231308271058693)
                  ·
                    refine ⟨3994537171543370300823505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21304198248231308271058693 3994537171543370300823505)
                    ·
                      refine ⟨2995902878657527725617629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994537171543370300823505 2995902878657527725617629)
                      ·
                        rfl

theorem cell23_5834500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5834500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834500 prefixEnd_5834500 := by exact prefixLift 5834500
  have htrace : WordTrace (prefixWord ++ tailWord_5834500) baseStart_5834500 baseEnd_5834500 := by
    simpa [prefixWord, tailWord_5834500, baseEnd_5834500] using wordTrace_append hprefix tailTrace_5834500
  have hstable : (prefixWord ++ tailWord_5834500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834500).length < 2 ^ (prefixWord ++ tailWord_5834500).sum := by decide
  have hdescent : baseEnd_5834500 < baseStart_5834500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834567 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_5834567 : Nat := 118140960795 + 5834567 * 2 ^ 59
def prefixEnd_5834567 : Nat := 4983230072969 + 3 ^ 40 * 5834567 * 2
def baseEnd_5834567 : Nat := 2995937281861378963479821

theorem tailTrace_5834567 : CollatzResearch.WordTrace tailWord_5834567 prefixEnd_5834567 2995937281861378963479821 := by
  unfold tailWord_5834567
  simp only [CollatzResearch.WordTrace]
  refine ⟨212804141053367698556101955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141869427368911799037401303 212804141053367698556101955)
  ·
    refine ⟨319206211580051547834152933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212804141053367698556101955 319206211580051547834152933)
    ·
      refine ⟨59851164671259665218903675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319206211580051547834152933 59851164671259665218903675)
      ·
        refine ⟨89776747006889497828355513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59851164671259665218903675 89776747006889497828355513)
        ·
          refine ⟨67332560255167123371266635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89776747006889497828355513 67332560255167123371266635)
          ·
            refine ⟨100998840382750685056899953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67332560255167123371266635 100998840382750685056899953)
            ·
              refine ⟨75749130287063013792674965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100998840382750685056899953 75749130287063013792674965)
              ·
                refine ⟨3550740482206078771531639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75749130287063013792674965 3550740482206078771531639)
                ·
                  refine ⟨5326110723309118157297459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550740482206078771531639 5326110723309118157297459)
                  ·
                    refine ⟨7989166084963677235946189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326110723309118157297459 7989166084963677235946189)
                    ·
                      refine ⟨2995937281861378963479821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989166084963677235946189 2995937281861378963479821)
                      ·
                        rfl

theorem cell23_5834567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_5834567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834567 prefixEnd_5834567 := by exact prefixLift 5834567
  have htrace : WordTrace (prefixWord ++ tailWord_5834567) baseStart_5834567 baseEnd_5834567 := by
    simpa [prefixWord, tailWord_5834567, baseEnd_5834567] using wordTrace_append hprefix tailTrace_5834567
  have hstable : (prefixWord ++ tailWord_5834567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834567).length < 2 ^ (prefixWord ++ tailWord_5834567).sum := by decide
  have hdescent : baseEnd_5834567 < baseStart_5834567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834594 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_5834594 : Nat := 118140960795 + 5834594 * 2 ^ 59
def prefixEnd_5834594 : Nat := 4983230072969 + 3 ^ 40 * 5834594 * 2
def baseEnd_5834594 : Nat := 2995951145839050357842197

theorem tailTrace_5834594 : CollatzResearch.WordTrace tailWord_5834594 prefixEnd_5834594 2995951145839050357842197 := by
  unfold tailWord_5834594
  simp only [CollatzResearch.WordTrace]
  refine ⟨53201281456067470541833709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141870083882846588111556557 53201281456067470541833709)
  ·
    refine ⟨19950480546025301453187641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53201281456067470541833709 19950480546025301453187641)
    ·
      refine ⟨14962860409518976089890731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19950480546025301453187641 14962860409518976089890731)
      ·
        refine ⟨22444290614278464134836097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14962860409518976089890731 22444290614278464134836097)
        ·
          refine ⟨16833217960708848101127073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22444290614278464134836097 16833217960708848101127073)
          ·
            refine ⟨12624913470531636075845305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16833217960708848101127073 12624913470531636075845305)
            ·
              refine ⟨9468685102898727056883979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624913470531636075845305 9468685102898727056883979)
              ·
                refine ⟨14203027654348090585325969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468685102898727056883979 14203027654348090585325969)
                ·
                  refine ⟨10652270740761067938994477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14203027654348090585325969 10652270740761067938994477)
                  ·
                    refine ⟨3994601527785400477122929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10652270740761067938994477 3994601527785400477122929)
                    ·
                      refine ⟨2995951145839050357842197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994601527785400477122929 2995951145839050357842197)
                      ·
                        rfl

theorem cell23_5834594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_5834594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834594 prefixEnd_5834594 := by exact prefixLift 5834594
  have htrace : WordTrace (prefixWord ++ tailWord_5834594) baseStart_5834594 baseEnd_5834594 := by
    simpa [prefixWord, tailWord_5834594, baseEnd_5834594] using wordTrace_append hprefix tailTrace_5834594
  have hstable : (prefixWord ++ tailWord_5834594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834594).length < 2 ^ (prefixWord ++ tailWord_5834594).sum := by decide
  have hdescent : baseEnd_5834594 < baseStart_5834594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834623 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_5834623 : Nat := 118140960795 + 5834623 * 2 ^ 59
def prefixEnd_5834623 : Nat := 4983230072969 + 3 ^ 40 * 5834623 * 2
def baseEnd_5834623 : Nat := 2995966036778030744379563

theorem tailTrace_5834623 : CollatzResearch.WordTrace tailWord_5834623 prefixEnd_5834623 2995966036778030744379563 := by
  unfold tailWord_5834623
  simp only [CollatzResearch.WordTrace]
  refine ⟨212806183541164820120140523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141870789027443213413427015 212806183541164820120140523)
  ·
    refine ⟨319209275311747230180210785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212806183541164820120140523 319209275311747230180210785)
    ·
      refine ⟨239406956483810422635158089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319209275311747230180210785 239406956483810422635158089)
      ·
        refine ⟨179555217362857816976368567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239406956483810422635158089 179555217362857816976368567)
        ·
          refine ⟨269332826044286725464552851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179555217362857816976368567 269332826044286725464552851)
          ·
            refine ⟨403999239066430088196829277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269332826044286725464552851 403999239066430088196829277)
            ·
              refine ⟨151499714649911283073810979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403999239066430088196829277 151499714649911283073810979)
              ·
                refine ⟨227249571974866924610716469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151499714649911283073810979 227249571974866924610716469)
                ·
                  refine ⟨21304647372643774182254669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227249571974866924610716469 21304647372643774182254669)
                  ·
                    refine ⟨7989242764741415318345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21304647372643774182254669 7989242764741415318345501)
                    ·
                      refine ⟨2995966036778030744379563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989242764741415318345501 2995966036778030744379563)
                      ·
                        rfl

theorem cell23_5834623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_5834623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834623 prefixEnd_5834623 := by exact prefixLift 5834623
  have htrace : WordTrace (prefixWord ++ tailWord_5834623) baseStart_5834623 baseEnd_5834623 := by
    simpa [prefixWord, tailWord_5834623, baseEnd_5834623] using wordTrace_append hprefix tailTrace_5834623
  have hstable : (prefixWord ++ tailWord_5834623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834623).length < 2 ^ (prefixWord ++ tailWord_5834623).sum := by decide
  have hdescent : baseEnd_5834623 < baseStart_5834623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834624 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 1, 2, 2]
def baseStart_5834624 : Nat := 118140960795 + 5834624 * 2 ^ 59
def prefixEnd_5834624 : Nat := 4983230072969 + 3 ^ 40 * 5834624 * 2
def baseEnd_5834624 : Nat := 2995966550258685240467059

theorem tailTrace_5834624 : CollatzResearch.WordTrace tailWord_5834624 prefixEnd_5834624 2995966550258685240467059 := by
  unfold tailWord_5834624
  simp only [CollatzResearch.WordTrace]
  refine ⟨106403110007080598645463463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141870813342774131527284617 106403110007080598645463463)
  ·
    refine ⟨159604665010620897968195195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106403110007080598645463463 159604665010620897968195195)
    ·
      refine ⟨239406997515931346952292793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159604665010620897968195195 239406997515931346952292793)
      ·
        refine ⟨179555248136948510214219595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239406997515931346952292793 179555248136948510214219595)
        ·
          refine ⟨269332872205422765321329393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179555248136948510214219595 269332872205422765321329393)
          ·
            refine ⟨201999654154067073990997045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269332872205422765321329393 201999654154067073990997045)
            ·
              refine ⟨18937467576943788186655973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201999654154067073990997045 18937467576943788186655973)
              ·
                refine ⟨3550775170676960284997995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18937467576943788186655973 3550775170676960284997995)
                ·
                  refine ⟨5326162756015440427496993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550775170676960284997995 5326162756015440427496993)
                  ·
                    refine ⟨3994622067011580320622745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326162756015440427496993 3994622067011580320622745)
                    ·
                      refine ⟨2995966550258685240467059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994622067011580320622745 2995966550258685240467059)
                      ·
                        rfl

theorem cell23_5834624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_5834624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834624 prefixEnd_5834624 := by exact prefixLift 5834624
  have htrace : WordTrace (prefixWord ++ tailWord_5834624) baseStart_5834624 baseEnd_5834624 := by
    simpa [prefixWord, tailWord_5834624, baseEnd_5834624] using wordTrace_append hprefix tailTrace_5834624
  have hstable : (prefixWord ++ tailWord_5834624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834624).length < 2 ^ (prefixWord ++ tailWord_5834624).sum := by decide
  have hdescent : baseEnd_5834624 < baseStart_5834624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834658 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5834658 : Nat := 118140960795 + 5834658 * 2 ^ 59
def prefixEnd_5834658 : Nat := 4983230072969 + 3 ^ 40 * 5834658 * 2
def baseEnd_5834658 : Nat := 2995984008600938107441903

theorem tailTrace_5834658 : CollatzResearch.WordTrace tailWord_5834658 prefixEnd_5834658 2995984008600938107441903 := by
  unfold tailWord_5834658
  simp only [CollatzResearch.WordTrace]
  refine ⟨53201865024009505274416157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141871640064025347398443085 53201865024009505274416157)
  ·
    refine ⟨19950699384003564477906059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53201865024009505274416157 19950699384003564477906059)
    ·
      refine ⟨29926049076005346716859089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19950699384003564477906059 29926049076005346716859089)
      ·
        refine ⟨22444536807004010037644317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29926049076005346716859089 22444536807004010037644317)
        ·
          refine ⟨8416701302626503764116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22444536807004010037644317 8416701302626503764116619)
          ·
            refine ⟨12625051953939755646174929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416701302626503764116619 12625051953939755646174929)
            ·
              refine ⟨9468788965454816734631197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12625051953939755646174929 9468788965454816734631197)
              ·
                refine ⟨3550795862045556275486699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9468788965454816734631197 3550795862045556275486699)
                ·
                  refine ⟨5326193793068334413230049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550795862045556275486699 5326193793068334413230049)
                  ·
                    refine ⟨3994645344801250809922537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326193793068334413230049 3994645344801250809922537)
                    ·
                      refine ⟨2995984008600938107441903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994645344801250809922537 2995984008600938107441903)
                      ·
                        rfl

theorem cell23_5834658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5834658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834658 prefixEnd_5834658 := by exact prefixLift 5834658
  have htrace : WordTrace (prefixWord ++ tailWord_5834658) baseStart_5834658 baseEnd_5834658 := by
    simpa [prefixWord, tailWord_5834658, baseEnd_5834658] using wordTrace_append hprefix tailTrace_5834658
  have hstable : (prefixWord ++ tailWord_5834658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834658).length < 2 ^ (prefixWord ++ tailWord_5834658).sum := by decide
  have hdescent : baseEnd_5834658 < baseStart_5834658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834693 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_5834693 : Nat := 118140960795 + 5834693 * 2 ^ 59
def prefixEnd_5834693 : Nat := 4983230072969 + 3 ^ 40 * 5834693 * 2
def baseEnd_5834693 : Nat := 2996001980423845470504241

theorem tailTrace_5834693 : CollatzResearch.WordTrace tailWord_5834693 prefixEnd_5834693 2996001980423845470504241 := by
  unfold tailWord_5834693
  simp only [CollatzResearch.WordTrace]
  refine ⟨212808736650911222075188733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141872491100607481383459155 212808736650911222075188733)
  ·
    refine ⟨79803276244091708278195775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212808736650911222075188733 79803276244091708278195775)
    ·
      refine ⟨119704914366137562417293663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79803276244091708278195775 119704914366137562417293663)
      ·
        refine ⟨179557371549206343625940495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119704914366137562417293663 179557371549206343625940495)
        ·
          refine ⟨269336057323809515438910743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179557371549206343625940495 269336057323809515438910743)
          ·
            refine ⟨404004085985714273158366115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269336057323809515438910743 404004085985714273158366115)
            ·
              refine ⟨606006128978571409737549173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404004085985714273158366115 606006128978571409737549173)
              ·
                refine ⟨56813074591741069662895235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 606006128978571409737549173 56813074591741069662895235)
                ·
                  refine ⟨85219611887611604494342853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56813074591741069662895235 85219611887611604494342853)
                  ·
                    refine ⟨15978677228927175842689285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85219611887611604494342853 15978677228927175842689285)
                    ·
                      refine ⟨2996001980423845470504241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15978677228927175842689285 2996001980423845470504241)
                      ·
                        rfl

theorem cell23_5834693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_5834693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834693 prefixEnd_5834693 := by exact prefixLift 5834693
  have htrace : WordTrace (prefixWord ++ tailWord_5834693) baseStart_5834693 baseEnd_5834693 := by
    simpa [prefixWord, tailWord_5834693, baseEnd_5834693] using wordTrace_append hprefix tailTrace_5834693
  have hstable : (prefixWord ++ tailWord_5834693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834693).length < 2 ^ (prefixWord ++ tailWord_5834693).sum := by decide
  have hdescent : baseEnd_5834693 < baseStart_5834693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834703 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 7]
def baseStart_5834703 : Nat := 118140960795 + 5834703 * 2 ^ 59
def prefixEnd_5834703 : Nat := 4983230072969 + 3 ^ 40 * 5834703 * 2
def baseEnd_5834703 : Nat := 332889679470043381264355

theorem tailTrace_5834703 : CollatzResearch.WordTrace tailWord_5834703 prefixEnd_5834703 332889679470043381264355 := by
  unfold tailWord_5834703
  simp only [CollatzResearch.WordTrace]
  refine ⟨212809101380874993783052763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141872734253916662522035175 212809101380874993783052763)
  ·
    refine ⟨319213652071312490674579145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212809101380874993783052763 319213652071312490674579145)
    ·
      refine ⟨239410239053484368005934359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319213652071312490674579145 239410239053484368005934359)
      ·
        refine ⟨359115358580226552008901539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239410239053484368005934359 359115358580226552008901539)
        ·
          refine ⟨538673037870339828013352309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359115358580226552008901539 538673037870339828013352309)
          ·
            refine ⟨50500597300344358876251779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 538673037870339828013352309 50500597300344358876251779)
            ·
              refine ⟨75750895950516538314377669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50500597300344358876251779 75750895950516538314377669)
              ·
                refine ⟨14203292990721850933945813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75750895950516538314377669 14203292990721850933945813)
                ·
                  refine ⟨332889679470043381264355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14203292990721850933945813 332889679470043381264355)
                  ·
                    rfl

theorem cell23_5834703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 7].length) (baseStart_5834703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834703 prefixEnd_5834703 := by exact prefixLift 5834703
  have htrace : WordTrace (prefixWord ++ tailWord_5834703) baseStart_5834703 baseEnd_5834703 := by
    simpa [prefixWord, tailWord_5834703, baseEnd_5834703] using wordTrace_append hprefix tailTrace_5834703
  have hstable : (prefixWord ++ tailWord_5834703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834703).length < 2 ^ (prefixWord ++ tailWord_5834703).sum := by decide
  have hdescent : baseEnd_5834703 < baseStart_5834703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834717 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5834717 : Nat := 118140960795 + 5834717 * 2 ^ 59
def prefixEnd_5834717 : Nat := 4983230072969 + 3 ^ 40 * 5834717 * 2
def baseEnd_5834717 : Nat := 2996014303959553376604131

theorem tailTrace_5834717 : CollatzResearch.WordTrace tailWord_5834717 prefixEnd_5834717 2996014303959553376604131 := by
  unfold tailWord_5834717
  simp only [CollatzResearch.WordTrace]
  refine ⟨212809612002824274174062405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141873074668549516116041603 212809612002824274174062405)
  ·
    refine ⟨39901802250529551407636701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212809612002824274174062405 39901802250529551407636701)
    ·
      refine ⟨14963175843948581777863763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39901802250529551407636701 14963175843948581777863763)
      ·
        refine ⟨22444763765922872666795645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963175843948581777863763 22444763765922872666795645)
        ·
          refine ⟨8416786412221077250048367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22444763765922872666795645 8416786412221077250048367)
          ·
            refine ⟨12625179618331615875072551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416786412221077250048367 12625179618331615875072551)
            ·
              refine ⟨18937769427497423812608827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625179618331615875072551 18937769427497423812608827)
              ·
                refine ⟨28406654141246135718913241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18937769427497423812608827 28406654141246135718913241)
                ·
                  refine ⟨21304990605934601789184931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28406654141246135718913241 21304990605934601789184931)
                  ·
                    refine ⟨31957485908901902683777397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21304990605934601789184931 31957485908901902683777397)
                    ·
                      refine ⟨2996014303959553376604131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31957485908901902683777397 2996014303959553376604131)
                      ·
                        rfl

theorem cell23_5834717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5834717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834717 prefixEnd_5834717 := by exact prefixLift 5834717
  have htrace : WordTrace (prefixWord ++ tailWord_5834717) baseStart_5834717 baseEnd_5834717 := by
    simpa [prefixWord, tailWord_5834717, baseEnd_5834717] using wordTrace_append hprefix tailTrace_5834717
  have hstable : (prefixWord ++ tailWord_5834717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834717).length < 2 ^ (prefixWord ++ tailWord_5834717).sum := by decide
  have hdescent : baseEnd_5834717 < baseStart_5834717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834737 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 7]
def baseStart_5834737 : Nat := 118140960795 + 5834737 * 2 ^ 59
def prefixEnd_5834737 : Nat := 4983230072969 + 3 ^ 40 * 5834737 * 2
def baseEnd_5834737 : Nat := 332891619285849255372671

theorem tailTrace_5834737 : CollatzResearch.WordTrace tailWord_5834737 prefixEnd_5834737 332891619285849255372671 := by
  unfold tailWord_5834737
  simp only [CollatzResearch.WordTrace]
  refine ⟨212810341462751817589790465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141873560975167878393193643 212810341462751817589790465)
  ·
    refine ⟨159607756097063863192342849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212810341462751817589790465 159607756097063863192342849)
    ·
      refine ⟨119705817072797897394257137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159607756097063863192342849 119705817072797897394257137)
      ·
        refine ⟨89779362804598423045692853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119705817072797897394257137 89779362804598423045692853)
        ·
          refine ⟨8416815262931102160533705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89779362804598423045692853 8416815262931102160533705)
          ·
            refine ⟨6312611447198326620400279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416815262931102160533705 6312611447198326620400279)
            ·
              refine ⟨9468917170797489930600419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312611447198326620400279 9468917170797489930600419)
              ·
                refine ⟨14203375756196234895900629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468917170797489930600419 14203375756196234895900629)
                ·
                  refine ⟨332891619285849255372671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14203375756196234895900629 332891619285849255372671)
                  ·
                    rfl

theorem cell23_5834737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_5834737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834737 prefixEnd_5834737 := by exact prefixLift 5834737
  have htrace : WordTrace (prefixWord ++ tailWord_5834737) baseStart_5834737 baseEnd_5834737 := by
    simpa [prefixWord, tailWord_5834737, baseEnd_5834737] using wordTrace_append hprefix tailTrace_5834737
  have hstable : (prefixWord ++ tailWord_5834737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834737).length < 2 ^ (prefixWord ++ tailWord_5834737).sum := by decide
  have hdescent : baseEnd_5834737 < baseStart_5834737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834787 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 2, 4, 2]
def baseStart_5834787 : Nat := 118140960795 + 5834787 * 2 ^ 59
def prefixEnd_5834787 : Nat := 4983230072969 + 3 ^ 40 * 5834787 * 2
def baseEnd_5834787 : Nat := 2996050247605368102728809

theorem tailTrace_5834787 : CollatzResearch.WordTrace tailWord_5834787 prefixEnd_5834787 2996050247605368102728809 := by
  unfold tailWord_5834787
  simp only [CollatzResearch.WordTrace]
  refine ⟨212812165112570676129110615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141874776741713784086073743 212812165112570676129110615)
  ·
    refine ⟨319218247668856014193665923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212812165112570676129110615 319218247668856014193665923)
    ·
      refine ⟨478827371503284021290498885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319218247668856014193665923 478827371503284021290498885)
      ·
        refine ⟨89780132156865753991968541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 478827371503284021290498885 89780132156865753991968541)
        ·
          refine ⟨33667549558824657746988203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89780132156865753991968541 33667549558824657746988203)
          ·
            refine ⟨50501324338236986620482305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33667549558824657746988203 50501324338236986620482305)
            ·
              refine ⟨37875993253677739965361729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50501324338236986620482305 37875993253677739965361729)
              ·
                refine ⟨28406994940258304974021297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37875993253677739965361729 28406994940258304974021297)
                ·
                  refine ⟨21305246205193728730515973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28406994940258304974021297 21305246205193728730515973)
                  ·
                    refine ⟨3994733663473824136971745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21305246205193728730515973 3994733663473824136971745)
                    ·
                      refine ⟨2996050247605368102728809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994733663473824136971745 2996050247605368102728809)
                      ·
                        rfl

theorem cell23_5834787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_5834787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834787 prefixEnd_5834787 := by exact prefixLift 5834787
  have htrace : WordTrace (prefixWord ++ tailWord_5834787) baseStart_5834787 baseEnd_5834787 := by
    simpa [prefixWord, tailWord_5834787, baseEnd_5834787] using wordTrace_append hprefix tailTrace_5834787
  have hstable : (prefixWord ++ tailWord_5834787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834787).length < 2 ^ (prefixWord ++ tailWord_5834787).sum := by decide
  have hdescent : baseEnd_5834787 < baseStart_5834787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834788 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 5]
def baseStart_5834788 : Nat := 118140960795 + 5834788 * 2 ^ 59
def prefixEnd_5834788 : Nat := 4983230072969 + 3 ^ 40 * 5834788 * 2
def baseEnd_5834788 : Nat := 332894529009558066535145

theorem tailTrace_5834788 : CollatzResearch.WordTrace tailWord_5834788 prefixEnd_5834788 332894529009558066535145 := by
  unfold tailWord_5834788
  simp only [CollatzResearch.WordTrace]
  refine ⟨106406100792783526649948509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141874801057044702199931345 106406100792783526649948509)
  ·
    refine ⟨39902287797293822493730691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106406100792783526649948509 39902287797293822493730691)
    ·
      refine ⟨59853431695940733740596037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39902287797293822493730691 59853431695940733740596037)
      ·
        refine ⟨11222518442988887576361757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59853431695940733740596037 11222518442988887576361757)
        ·
          refine ⟨4208444416120832841135659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11222518442988887576361757 4208444416120832841135659)
          ·
            refine ⟨6312666624181249261703489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208444416120832841135659 6312666624181249261703489)
            ·
              refine ⟨4734499968135936946277617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6312666624181249261703489 4734499968135936946277617)
              ·
                refine ⟨3550874976101952709708213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734499968135936946277617 3550874976101952709708213)
                ·
                  refine ⟨332894529009558066535145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550874976101952709708213 332894529009558066535145)
                  ·
                    rfl

theorem cell23_5834788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_5834788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834788 prefixEnd_5834788 := by exact prefixLift 5834788
  have htrace : WordTrace (prefixWord ++ tailWord_5834788) baseStart_5834788 baseEnd_5834788 := by
    simpa [prefixWord, tailWord_5834788, baseEnd_5834788] using wordTrace_append hprefix tailTrace_5834788
  have hstable : (prefixWord ++ tailWord_5834788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834788).length < 2 ^ (prefixWord ++ tailWord_5834788).sum := by decide
  have hdescent : baseEnd_5834788 < baseStart_5834788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834793 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 14]
def baseStart_5834793 : Nat := 118140960795 + 5834793 * 2 ^ 59
def prefixEnd_5834793 : Nat := 4983230072969 + 3 ^ 40 * 5834793 * 2
def baseEnd_5834793 : Nat := 332894814276588342139309

theorem tailTrace_5834793 : CollatzResearch.WordTrace tailWord_5834793 prefixEnd_5834793 332894814276588342139309 := by
  unfold tailWord_5834793
  simp only [CollatzResearch.WordTrace]
  refine ⟨212812383950548939153829033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141874922633699292769219355 212812383950548939153829033)
  ·
    refine ⟨159609287962911704365371775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212812383950548939153829033 159609287962911704365371775)
    ·
      refine ⟨239413931944367556548057663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159609287962911704365371775 239413931944367556548057663)
      ·
        refine ⟨359120897916551334822086495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239413931944367556548057663 359120897916551334822086495)
        ·
          refine ⟨538681346874827002233129743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359120897916551334822086495 538681346874827002233129743)
          ·
            refine ⟨808022020312240503349694615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538681346874827002233129743 808022020312240503349694615)
            ·
              refine ⟨1212033030468360755024541923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808022020312240503349694615 1212033030468360755024541923)
              ·
                refine ⟨1818049545702541132536812885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212033030468360755024541923 1818049545702541132536812885)
                ·
                  refine ⟨332894814276588342139309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 1818049545702541132536812885 332894814276588342139309)
                  ·
                    rfl

theorem cell23_5834793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_5834793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834793 prefixEnd_5834793 := by exact prefixLift 5834793
  have htrace : WordTrace (prefixWord ++ tailWord_5834793) baseStart_5834793 baseEnd_5834793 := by
    simpa [prefixWord, tailWord_5834793, baseEnd_5834793] using wordTrace_append hprefix tailTrace_5834793
  have hstable : (prefixWord ++ tailWord_5834793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834793).length < 2 ^ (prefixWord ++ tailWord_5834793).sum := by decide
  have hdescent : baseEnd_5834793 < baseStart_5834793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834844 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 6]
def baseStart_5834844 : Nat := 118140960795 + 5834844 * 2 ^ 59
def prefixEnd_5834844 : Nat := 4983230072969 + 3 ^ 40 * 5834844 * 2
def baseEnd_5834844 : Nat := 332897724000297153301783

theorem tailTrace_5834844 : CollatzResearch.WordTrace tailWord_5834844 prefixEnd_5834844 332897724000297153301783 := by
  unfold tailWord_5834844
  simp only [CollatzResearch.WordTrace]
  refine ⟨106407122036682087431967793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141876162715576116575957057 106407122036682087431967793)
  ·
    refine ⟨79805341527511565573975845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106407122036682087431967793 79805341527511565573975845)
    ·
      refine ⟨14963501536408418545120471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79805341527511565573975845 14963501536408418545120471)
      ·
        refine ⟨22445252304612627817680707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963501536408418545120471 22445252304612627817680707)
        ·
          refine ⟨33667878456918941726521061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22445252304612627817680707 33667878456918941726521061)
          ·
            refine ⟨6312727210672301573722699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33667878456918941726521061 6312727210672301573722699)
            ·
              refine ⟨9469090816008452360584049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312727210672301573722699 9469090816008452360584049)
              ·
                refine ⟨7101818112006339270438037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9469090816008452360584049 7101818112006339270438037)
                ·
                  refine ⟨332897724000297153301783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7101818112006339270438037 332897724000297153301783)
                  ·
                    rfl

theorem cell23_5834844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_5834844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834844 prefixEnd_5834844 := by exact prefixLift 5834844
  have htrace : WordTrace (prefixWord ++ tailWord_5834844) baseStart_5834844 baseEnd_5834844 := by
    simpa [prefixWord, tailWord_5834844, baseEnd_5834844] using wordTrace_append hprefix tailTrace_5834844
  have hstable : (prefixWord ++ tailWord_5834844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834844).length < 2 ^ (prefixWord ++ tailWord_5834844).sum := by decide
  have hdescent : baseEnd_5834844 < baseStart_5834844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834880 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_5834880 : Nat := 118140960795 + 5834880 * 2 ^ 59
def prefixEnd_5834880 : Nat := 4983230072969 + 3 ^ 40 * 5834880 * 2
def baseEnd_5834880 : Nat := 2996098001306236238865881

theorem tailTrace_5834880 : CollatzResearch.WordTrace tailWord_5834880 prefixEnd_5834880 2996098001306236238865881 := by
  unfold tailWord_5834880
  simp only [CollatzResearch.WordTrace]
  refine ⟨106407778550616876506123047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141877038067489168674830729 106407778550616876506123047)
  ·
    refine ⟨159611667825925314759184571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106407778550616876506123047 159611667825925314759184571)
    ·
      refine ⟨239417501738887972138776857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159611667825925314759184571 239417501738887972138776857)
      ·
        refine ⟨179563126304165979104082643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239417501738887972138776857 179563126304165979104082643)
        ·
          refine ⟨269344689456248968656123965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179563126304165979104082643 269344689456248968656123965)
          ·
            refine ⟨101004258546093363246046487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269344689456248968656123965 101004258546093363246046487)
            ·
              refine ⟨151506387819140044869069731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101004258546093363246046487 151506387819140044869069731)
              ·
                refine ⟨227259581728710067303604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151506387819140044869069731 227259581728710067303604597)
                ·
                  refine ⟨21305585787066568809712931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227259581728710067303604597 21305585787066568809712931)
                  ·
                    refine ⟨31958378680599853214569397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21305585787066568809712931 31958378680599853214569397)
                    ·
                      refine ⟨2996098001306236238865881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31958378680599853214569397 2996098001306236238865881)
                      ·
                        rfl

theorem cell23_5834880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_5834880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834880 prefixEnd_5834880 := by exact prefixLift 5834880
  have htrace : WordTrace (prefixWord ++ tailWord_5834880) baseStart_5834880 baseEnd_5834880 := by
    simpa [prefixWord, tailWord_5834880, baseEnd_5834880] using wordTrace_append hprefix tailTrace_5834880
  have hstable : (prefixWord ++ tailWord_5834880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834880).length < 2 ^ (prefixWord ++ tailWord_5834880).sum := by decide
  have hdescent : baseEnd_5834880 < baseStart_5834880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834887 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 4, 4]
def baseStart_5834887 : Nat := 118140960795 + 5834887 * 2 ^ 59
def prefixEnd_5834887 : Nat := 4983230072969 + 3 ^ 40 * 5834887 * 2
def baseEnd_5834887 : Nat := 998700531890272570492783

theorem tailTrace_5834887 : CollatzResearch.WordTrace tailWord_5834887 prefixEnd_5834887 998700531890272570492783 := by
  unfold tailWord_5834887
  simp only [CollatzResearch.WordTrace]
  refine ⟨212815812412208393207750915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141877208274805595471833943 212815812412208393207750915)
  ·
    refine ⟨319223718618312589811626373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212815812412208393207750915 319223718618312589811626373)
    ·
      refine ⟨59854447240933610589679945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319223718618312589811626373 59854447240933610589679945)
      ·
        refine ⟨44890835430700207942259959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59854447240933610589679945 44890835430700207942259959)
        ·
          refine ⟨67336253146050311913389939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44890835430700207942259959 67336253146050311913389939)
          ·
            refine ⟨101004379719075467870084909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67336253146050311913389939 101004379719075467870084909)
            ·
              refine ⟨37876642394653300451281841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101004379719075467870084909 37876642394653300451281841)
              ·
                refine ⟨28407481795989975338461381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37876642394653300451281841 28407481795989975338461381)
                ·
                  refine ⟨5326402836748120375961509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28407481795989975338461381 5326402836748120375961509)
                  ·
                    refine ⟨998700531890272570492783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5326402836748120375961509 998700531890272570492783)
                    ·
                      rfl

theorem cell23_5834887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_5834887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834887 prefixEnd_5834887 := by exact prefixLift 5834887
  have htrace : WordTrace (prefixWord ++ tailWord_5834887) baseStart_5834887 baseEnd_5834887 := by
    simpa [prefixWord, tailWord_5834887, baseEnd_5834887] using wordTrace_append hprefix tailTrace_5834887
  have hstable : (prefixWord ++ tailWord_5834887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834887).length < 2 ^ (prefixWord ++ tailWord_5834887).sum := by decide
  have hdescent : baseEnd_5834887 < baseStart_5834887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834888 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5834888 : Nat := 118140960795 + 5834888 * 2 ^ 59
def prefixEnd_5834888 : Nat := 4983230072969 + 3 ^ 40 * 5834888 * 2
def baseEnd_5834888 : Nat := 2996102109151472207565845

theorem tailTrace_5834888 : CollatzResearch.WordTrace tailWord_5834888 prefixEnd_5834888 2996102109151472207565845 := by
  unfold tailWord_5834888
  simp only [CollatzResearch.WordTrace]
  refine ⟨106407924442602385189268659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141877232590136513585691545 106407924442602385189268659)
  ·
    refine ⟨159611886663903577783902989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106407924442602385189268659 159611886663903577783902989)
    ·
      refine ⟨59854457498963841668963621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159611886663903577783902989 59854457498963841668963621)
      ·
        refine ⟨11222710781055720312930679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59854457498963841668963621 11222710781055720312930679)
        ·
          refine ⟨16834066171583580469396019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11222710781055720312930679 16834066171583580469396019)
          ·
            refine ⟨25251099257375370704094029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16834066171583580469396019 25251099257375370704094029)
            ·
              refine ⟨9469162221515764014035261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25251099257375370704094029 9469162221515764014035261)
              ·
                refine ⟨3550935833068411505263223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9469162221515764014035261 3550935833068411505263223)
                ·
                  refine ⟨5326403749602617257894835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550935833068411505263223 5326403749602617257894835)
                  ·
                    refine ⟨7989605624403925886842253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326403749602617257894835 7989605624403925886842253)
                    ·
                      refine ⟨2996102109151472207565845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989605624403925886842253 2996102109151472207565845)
                      ·
                        rfl

theorem cell23_5834888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5834888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834888 prefixEnd_5834888 := by exact prefixLift 5834888
  have htrace : WordTrace (prefixWord ++ tailWord_5834888) baseStart_5834888 baseEnd_5834888 := by
    simpa [prefixWord, tailWord_5834888, baseEnd_5834888] using wordTrace_append hprefix tailTrace_5834888
  have hstable : (prefixWord ++ tailWord_5834888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834888).length < 2 ^ (prefixWord ++ tailWord_5834888).sum := by decide
  have hdescent : baseEnd_5834888 < baseStart_5834888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834914 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5834914 : Nat := 118140960795 + 5834914 * 2 ^ 59
def prefixEnd_5834914 : Nat := 4983230072969 + 3 ^ 40 * 5834914 * 2
def baseEnd_5834914 : Nat := 2996115459648489105840725

theorem tailTrace_5834914 : CollatzResearch.WordTrace tailWord_5834914 prefixEnd_5834914 2996115459648489105840725 := by
  unfold tailWord_5834914
  simp only [CollatzResearch.WordTrace]
  refine ⟨53204199295777644204745949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141877864788740384545989197 53204199295777644204745949)
  ·
    refine ⟨19951574735916616576779731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53204199295777644204745949 19951574735916616576779731)
    ·
      refine ⟨29927362103874924865169597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19951574735916616576779731 29927362103874924865169597)
      ·
        refine ⟨11222760788953096824438599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29927362103874924865169597 11222760788953096824438599)
        ·
          refine ⟨16834141183429645236657899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11222760788953096824438599 16834141183429645236657899)
          ·
            refine ⟨25251211775144467854986849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16834141183429645236657899 25251211775144467854986849)
            ·
              refine ⟨18938408831358350891240137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25251211775144467854986849 18938408831358350891240137)
              ·
                refine ⟨14203806623518763168430103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18938408831358350891240137 14203806623518763168430103)
                ·
                  refine ⟨21305709935278144752645155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14203806623518763168430103 21305709935278144752645155)
                  ·
                    refine ⟨31958564902917217128967733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21305709935278144752645155 31958564902917217128967733)
                    ·
                      refine ⟨2996115459648489105840725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31958564902917217128967733 2996115459648489105840725)
                      ·
                        rfl

theorem cell23_5834914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5834914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834914 prefixEnd_5834914 := by exact prefixLift 5834914
  have htrace : WordTrace (prefixWord ++ tailWord_5834914) baseStart_5834914 baseEnd_5834914 := by
    simpa [prefixWord, tailWord_5834914, baseEnd_5834914] using wordTrace_append hprefix tailTrace_5834914
  have hstable : (prefixWord ++ tailWord_5834914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834914).length < 2 ^ (prefixWord ++ tailWord_5834914).sum := by decide
  have hdescent : baseEnd_5834914 < baseStart_5834914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834927 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_5834927 : Nat := 118140960795 + 5834927 * 2 ^ 59
def prefixEnd_5834927 : Nat := 4983230072969 + 3 ^ 40 * 5834927 * 2
def baseEnd_5834927 : Nat := 2996122134896997554978165

theorem tailTrace_5834927 : CollatzResearch.WordTrace tailWord_5834927 prefixEnd_5834927 2996122134896997554978165 := by
  unfold tailWord_5834927
  simp only [CollatzResearch.WordTrace]
  refine ⟨212817271332063480039207035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141878180888042320026138023 212817271332063480039207035)
  ·
    refine ⟨319225906998095220058810553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212817271332063480039207035 319225906998095220058810553)
    ·
      refine ⟨239419430248571415044107915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319225906998095220058810553 239419430248571415044107915)
      ·
        refine ⟨359129145372857122566161873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239419430248571415044107915 359129145372857122566161873)
        ·
          refine ⟨269346859029642841924621405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359129145372857122566161873 269346859029642841924621405)
          ·
            refine ⟨101005072136116065721733027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269346859029642841924621405 101005072136116065721733027)
            ·
              refine ⟨151507608204174098582599541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101005072136116065721733027 151507608204174098582599541)
              ·
                refine ⟨14203838269141321742118707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151507608204174098582599541 14203838269141321742118707)
                ·
                  refine ⟨21305757403711982613178061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14203838269141321742118707 21305757403711982613178061)
                  ·
                    refine ⟨7989659026391993479941773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21305757403711982613178061 7989659026391993479941773)
                    ·
                      refine ⟨2996122134896997554978165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989659026391993479941773 2996122134896997554978165)
                      ·
                        rfl

theorem cell23_5834927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_5834927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834927 prefixEnd_5834927 := by exact prefixLift 5834927
  have htrace : WordTrace (prefixWord ++ tailWord_5834927) baseStart_5834927 baseEnd_5834927 := by
    simpa [prefixWord, tailWord_5834927, baseEnd_5834927] using wordTrace_append hprefix tailTrace_5834927
  have hstable : (prefixWord ++ tailWord_5834927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834927).length < 2 ^ (prefixWord ++ tailWord_5834927).sum := by decide
  have hdescent : baseEnd_5834927 < baseStart_5834927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834932 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5834932 : Nat := 118140960795 + 5834932 * 2 ^ 59
def prefixEnd_5834932 : Nat := 4983230072969 + 3 ^ 40 * 5834932 * 2
def baseEnd_5834932 : Nat := 2996124702300270035415643

theorem tailTrace_5834932 : CollatzResearch.WordTrace tailWord_5834932 prefixEnd_5834932 2996124702300270035415643 := by
  unfold tailWord_5834932
  simp only [CollatzResearch.WordTrace]
  refine ⟨106408726848522682946569525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141878302464696910595426033 106408726848522682946569525)
  ·
    refine ⟨9975818142049001526240893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106408726848522682946569525 9975818142049001526240893)
    ·
      refine ⟨3740931803268375572340335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9975818142049001526240893 3740931803268375572340335)
      ·
        refine ⟨5611397704902563358510503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740931803268375572340335 5611397704902563358510503)
        ·
          refine ⟨8417096557353845037765755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611397704902563358510503 8417096557353845037765755)
          ·
            refine ⟨12625644836030767556648633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8417096557353845037765755 12625644836030767556648633)
            ·
              refine ⟨9469233627023075667486475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12625644836030767556648633 9469233627023075667486475)
              ·
                refine ⟨14203850440534613501229713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9469233627023075667486475 14203850440534613501229713)
                ·
                  refine ⟨10652887830400960125922285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14203850440534613501229713 10652887830400960125922285)
                  ·
                    refine ⟨3994832936400360047220857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10652887830400960125922285 3994832936400360047220857)
                    ·
                      refine ⟨2996124702300270035415643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994832936400360047220857 2996124702300270035415643)
                      ·
                        rfl

theorem cell23_5834932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5834932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834932 prefixEnd_5834932 := by exact prefixLift 5834932
  have htrace : WordTrace (prefixWord ++ tailWord_5834932) baseStart_5834932 baseEnd_5834932 := by
    simpa [prefixWord, tailWord_5834932, baseEnd_5834932] using wordTrace_append hprefix tailTrace_5834932
  have hstable : (prefixWord ++ tailWord_5834932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834932).length < 2 ^ (prefixWord ++ tailWord_5834932).sum := by decide
  have hdescent : baseEnd_5834932 < baseStart_5834932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834944 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_5834944 : Nat := 118140960795 + 5834944 * 2 ^ 59
def prefixEnd_5834944 : Nat := 4983230072969 + 3 ^ 40 * 5834944 * 2
def baseEnd_5834944 : Nat := 2996130864068123988465587

theorem tailTrace_5834944 : CollatzResearch.WordTrace tailWord_5834944 prefixEnd_5834944 2996130864068123988465587 := by
  unfold tailWord_5834944
  simp only [CollatzResearch.WordTrace]
  refine ⟨106408945686500945971287943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141878594248667927961717257 106408945686500945971287943)
  ·
    refine ⟨159613418529751418956931915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106408945686500945971287943 159613418529751418956931915)
    ·
      refine ⟨239420127794627128435397873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159613418529751418956931915 239420127794627128435397873)
      ·
        refine ⟨179565095845970346326548405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239420127794627128435397873 179565095845970346326548405)
        ·
          refine ⟨16834227735559719968113913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179565095845970346326548405 16834227735559719968113913)
          ·
            refine ⟨12625670801669789976085435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16834227735559719968113913 12625670801669789976085435)
            ·
              refine ⟨18938506202504684964128153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625670801669789976085435 18938506202504684964128153)
              ·
                refine ⟨14203879651878513723096115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18938506202504684964128153 14203879651878513723096115)
                ·
                  refine ⟨21305819477817770584644173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14203879651878513723096115 21305819477817770584644173)
                  ·
                    refine ⟨7989682304181663969241565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21305819477817770584644173 7989682304181663969241565)
                    ·
                      refine ⟨2996130864068123988465587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989682304181663969241565 2996130864068123988465587)
                      ·
                        rfl

theorem cell23_5834944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_5834944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834944 prefixEnd_5834944 := by exact prefixLift 5834944
  have htrace : WordTrace (prefixWord ++ tailWord_5834944) baseStart_5834944 baseEnd_5834944 := by
    simpa [prefixWord, tailWord_5834944, baseEnd_5834944] using wordTrace_append hprefix tailTrace_5834944
  have hstable : (prefixWord ++ tailWord_5834944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834944).length < 2 ^ (prefixWord ++ tailWord_5834944).sum := by decide
  have hdescent : baseEnd_5834944 < baseStart_5834944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834948 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5834948 : Nat := 118140960795 + 5834948 * 2 ^ 59
def prefixEnd_5834948 : Nat := 4983230072969 + 3 ^ 40 * 5834948 * 2
def baseEnd_5834948 : Nat := 2996132917990741972815569

theorem tailTrace_5834948 : CollatzResearch.WordTrace tailWord_5834948 prefixEnd_5834948 2996132917990741972815569 := by
  unfold tailWord_5834948
  simp only [CollatzResearch.WordTrace]
  refine ⟨106409018632493700312860749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141878691509991600417147665 106409018632493700312860749)
  ·
    refine ⟨39903381987185137617322781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106409018632493700312860749 39903381987185137617322781)
    ·
      refine ⟨14963768245194426606496043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39903381987185137617322781 14963768245194426606496043)
      ·
        refine ⟨22445652367791639909744065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963768245194426606496043 22445652367791639909744065)
        ·
          refine ⟨16834239275843729932308049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22445652367791639909744065 16834239275843729932308049)
          ·
            refine ⟨12625679456882797449231037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16834239275843729932308049 12625679456882797449231037)
            ·
              refine ⟨4734629796331049043461639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12625679456882797449231037 4734629796331049043461639)
              ·
                refine ⟨7101944694496573565192459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734629796331049043461639 7101944694496573565192459)
                ·
                  refine ⟨10652917041744860347788689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7101944694496573565192459 10652917041744860347788689)
                  ·
                    refine ⟨7989687781308645260841517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10652917041744860347788689 7989687781308645260841517)
                    ·
                      refine ⟨2996132917990741972815569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989687781308645260841517 2996132917990741972815569)
                      ·
                        rfl

theorem cell23_5834948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5834948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834948 prefixEnd_5834948 := by exact prefixLift 5834948
  have htrace : WordTrace (prefixWord ++ tailWord_5834948) baseStart_5834948 baseEnd_5834948 := by
    simpa [prefixWord, tailWord_5834948, baseEnd_5834948] using wordTrace_append hprefix tailTrace_5834948
  have hstable : (prefixWord ++ tailWord_5834948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834948).length < 2 ^ (prefixWord ++ tailWord_5834948).sum := by decide
  have hdescent : baseEnd_5834948 < baseStart_5834948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834960 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_5834960 : Nat := 118140960795 + 5834960 * 2 ^ 59
def prefixEnd_5834960 : Nat := 4983230072969 + 3 ^ 40 * 5834960 * 2
def baseEnd_5834960 : Nat := 998713026586198641955171

theorem tailTrace_5834960 : CollatzResearch.WordTrace tailWord_5834960 prefixEnd_5834960 998713026586198641955171 := by
  unfold tailWord_5834960
  simp only [CollatzResearch.WordTrace]
  refine ⟨106409237470471963337579167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141878983293962617783438889 106409237470471963337579167)
  ·
    refine ⟨159613856205707945006368751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106409237470471963337579167 159613856205707945006368751)
    ·
      refine ⟨239420784308561917509553127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159613856205707945006368751 239420784308561917509553127)
      ·
        refine ⟨359131176462842876264329691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239420784308561917509553127 359131176462842876264329691)
        ·
          refine ⟨538696764694264314396494537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359131176462842876264329691 538696764694264314396494537)
          ·
            refine ⟨404022573520698235797370903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538696764694264314396494537 404022573520698235797370903)
            ·
              refine ⟨606033860281047353696056355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404022573520698235797370903 606033860281047353696056355)
              ·
                refine ⟨909050790421571030544084533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606033860281047353696056355 909050790421571030544084533)
                ·
                  refine ⟨85223511602022284113507925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 909050790421571030544084533 85223511602022284113507925)
                  ·
                    refine ⟨998713026586198641955171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85223511602022284113507925 998713026586198641955171)
                    ·
                      rfl

theorem cell23_5834960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_5834960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834960 prefixEnd_5834960 := by exact prefixLift 5834960
  have htrace : WordTrace (prefixWord ++ tailWord_5834960) baseStart_5834960 baseEnd_5834960 := by
    simpa [prefixWord, tailWord_5834960, baseEnd_5834960] using wordTrace_append hprefix tailTrace_5834960
  have hstable : (prefixWord ++ tailWord_5834960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834960).length < 2 ^ (prefixWord ++ tailWord_5834960).sum := by decide
  have hdescent : baseEnd_5834960 < baseStart_5834960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834962 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_5834962 : Nat := 118140960795 + 5834962 * 2 ^ 59
def prefixEnd_5834962 : Nat := 4983230072969 + 3 ^ 40 * 5834962 * 2
def baseEnd_5834962 : Nat := 2996140106719904918040505

theorem tailTrace_5834962 : CollatzResearch.WordTrace tailWord_5834962 prefixEnd_5834962 2996140106719904918040505 := by
  unfold tailWord_5834962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53204636971734170254182785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141879031924624454011154093 53204636971734170254182785)
  ·
    refine ⟨39903477728800627690637089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53204636971734170254182785 39903477728800627690637089)
    ·
      refine ⟨29927608296600470767977817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39903477728800627690637089 29927608296600470767977817)
      ·
        refine ⟨22445706222450353075983363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29927608296600470767977817 22445706222450353075983363)
        ·
          refine ⟨33668559333675529613975045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22445706222450353075983363 33668559333675529613975045)
          ·
            refine ⟨6312854875064161802620321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33668559333675529613975045 6312854875064161802620321)
            ·
              refine ⟨4734641156298121351965241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6312854875064161802620321 4734641156298121351965241)
              ·
                refine ⟨3550980867223591013973931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734641156298121351965241 3550980867223591013973931)
                ·
                  refine ⟨5326471300835386520960897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550980867223591013973931 5326471300835386520960897)
                  ·
                    refine ⟨3994853475626539890720673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326471300835386520960897 3994853475626539890720673)
                    ·
                      refine ⟨2996140106719904918040505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994853475626539890720673 2996140106719904918040505)
                      ·
                        rfl

theorem cell23_5834962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_5834962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834962 prefixEnd_5834962 := by exact prefixLift 5834962
  have htrace : WordTrace (prefixWord ++ tailWord_5834962) baseStart_5834962 baseEnd_5834962 := by
    simpa [prefixWord, tailWord_5834962, baseEnd_5834962] using wordTrace_append hprefix tailTrace_5834962
  have hstable : (prefixWord ++ tailWord_5834962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834962).length < 2 ^ (prefixWord ++ tailWord_5834962).sum := by decide
  have hdescent : baseEnd_5834962 < baseStart_5834962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834977 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_5834977 : Nat := 118140960795 + 5834977 * 2 ^ 59
def prefixEnd_5834977 : Nat := 4983230072969 + 3 ^ 40 * 5834977 * 2
def baseEnd_5834977 : Nat := 998715936309907453117645

theorem tailTrace_5834977 : CollatzResearch.WordTrace tailWord_5834977 prefixEnd_5834977 998715936309907453117645 := by
  unfold tailWord_5834977
  simp only [CollatzResearch.WordTrace]
  refine ⟨212819094981882338578527185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141879396654588225719018123 212819094981882338578527185)
  ·
    refine ⟨159614321236411753933895389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212819094981882338578527185 159614321236411753933895389)
    ·
      refine ⟨59855370463654407725210771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159614321236411753933895389 59855370463654407725210771)
      ·
        refine ⟨89783055695481611587816157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59855370463654407725210771 89783055695481611587816157)
        ·
          refine ⟨33668645885805604345431059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89783055695481611587816157 33668645885805604345431059)
          ·
            refine ⟨50502968828708406518146589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33668645885805604345431059 50502968828708406518146589)
            ·
              refine ⟨18938613310765652444304971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50502968828708406518146589 18938613310765652444304971)
              ·
                refine ⟨28407919966148478666457457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18938613310765652444304971 28407919966148478666457457)
                ·
                  refine ⟨21305939974611358999843093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28407919966148478666457457 21305939974611358999843093)
                  ·
                    refine ⟨998715936309907453117645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21305939974611358999843093 998715936309907453117645)
                    ·
                      rfl

theorem cell23_5834977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_5834977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834977 prefixEnd_5834977 := by exact prefixLift 5834977
  have htrace : WordTrace (prefixWord ++ tailWord_5834977) baseStart_5834977 baseEnd_5834977 := by
    simpa [prefixWord, tailWord_5834977, baseEnd_5834977] using wordTrace_append hprefix tailTrace_5834977
  have hstable : (prefixWord ++ tailWord_5834977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834977).length < 2 ^ (prefixWord ++ tailWord_5834977).sum := by decide
  have hdescent : baseEnd_5834977 < baseStart_5834977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5834987 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3]
def baseStart_5834987 : Nat := 118140960795 + 5834987 * 2 ^ 59
def prefixEnd_5834987 : Nat := 4983230072969 + 3 ^ 40 * 5834987 * 2
def baseEnd_5834987 : Nat := 2996152943736267320227889

theorem tailTrace_5834987 : CollatzResearch.WordTrace tailWord_5834987 prefixEnd_5834987 2996152943736267320227889 := by
  unfold tailWord_5834987
  simp only [CollatzResearch.WordTrace]
  refine ⟨212819459711846110286391215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141879639807897406857594143 212819459711846110286391215)
  ·
    refine ⟨319229189567769165429586823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212819459711846110286391215 319229189567769165429586823)
    ·
      refine ⟨478843784351653748144380235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319229189567769165429586823 478843784351653748144380235)
      ·
        refine ⟨718265676527480622216570353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478843784351653748144380235 718265676527480622216570353)
        ·
          refine ⟨538699257395610466662427765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718265676527480622216570353 538699257395610466662427765)
          ·
            refine ⟨50503055380838481249602603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 538699257395610466662427765 50503055380838481249602603)
            ·
              refine ⟨75754583071257721874403905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50503055380838481249602603 75754583071257721874403905)
              ·
                refine ⟨56815937303443291405802929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75754583071257721874403905 56815937303443291405802929)
                ·
                  refine ⟨42611952977582468554352197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56815937303443291405802929 42611952977582468554352197)
                  ·
                    refine ⟨7989741183296712853941037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42611952977582468554352197 7989741183296712853941037)
                    ·
                      refine ⟨2996152943736267320227889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989741183296712853941037 2996152943736267320227889)
                      ·
                        rfl

theorem cell23_5834987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3].length) (baseStart_5834987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5834987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5834987 prefixEnd_5834987 := by exact prefixLift 5834987
  have htrace : WordTrace (prefixWord ++ tailWord_5834987) baseStart_5834987 baseEnd_5834987 := by
    simpa [prefixWord, tailWord_5834987, baseEnd_5834987] using wordTrace_append hprefix tailTrace_5834987
  have hstable : (prefixWord ++ tailWord_5834987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5834987).length < 2 ^ (prefixWord ++ tailWord_5834987).sum := by decide
  have hdescent : baseEnd_5834987 < baseStart_5834987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5834987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835018 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_5835018 : Nat := 118140960795 + 5835018 * 2 ^ 59
def prefixEnd_5835018 : Nat := 4983230072969 + 3 ^ 40 * 5835018 * 2
def baseEnd_5835018 : Nat := 2996168861636556698940247

theorem tailTrace_5835018 : CollatzResearch.WordTrace tailWord_5835018 prefixEnd_5835018 2996168861636556698940247 := by
  unfold tailWord_5835018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53205147593683450645192427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141880393583155868387179805 53205147593683450645192427)
  ·
    refine ⟨79807721390525175967788641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53205147593683450645192427 79807721390525175967788641)
    ·
      refine ⟨59855791042893881975841481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79807721390525175967788641 59855791042893881975841481)
      ·
        refine ⟨44891843282170411481881111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59855791042893881975841481 44891843282170411481881111)
        ·
          refine ⟨67337764923255617222821667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44891843282170411481881111 67337764923255617222821667)
          ·
            refine ⟨101006647384883425834232501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67337764923255617222821667 101006647384883425834232501)
            ·
              refine ⟨9469373192332821171959297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101006647384883425834232501 9469373192332821171959297)
              ·
                refine ⟨7102029894249615878969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9469373192332821171959297 7102029894249615878969473)
                ·
                  refine ⟨5326522420687211909227105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102029894249615878969473 5326522420687211909227105)
                  ·
                    refine ⟨3994891815515408931920329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326522420687211909227105 3994891815515408931920329)
                    ·
                      refine ⟨2996168861636556698940247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994891815515408931920329 2996168861636556698940247)
                      ·
                        rfl

theorem cell23_5835018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_5835018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835018 prefixEnd_5835018 := by exact prefixLift 5835018
  have htrace : WordTrace (prefixWord ++ tailWord_5835018) baseStart_5835018 baseEnd_5835018 := by
    simpa [prefixWord, tailWord_5835018, baseEnd_5835018] using wordTrace_append hprefix tailTrace_5835018
  have hstable : (prefixWord ++ tailWord_5835018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835018).length < 2 ^ (prefixWord ++ tailWord_5835018).sum := by decide
  have hdescent : baseEnd_5835018 < baseStart_5835018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835058 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_5835058 : Nat := 118140960795 + 5835058 * 2 ^ 59
def prefixEnd_5835058 : Nat := 4983230072969 + 3 ^ 40 * 5835058 * 2
def baseEnd_5835058 : Nat := 332909933429192949160007

theorem tailTrace_5835058 : CollatzResearch.WordTrace tailWord_5835058 prefixEnd_5835058 332909933429192949160007 := by
  unfold tailWord_5835058
  simp only [CollatzResearch.WordTrace]
  refine ⟨53205512323647222353056457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141881366196392592941483885 53205512323647222353056457)
  ·
    refine ⟨39904134242735416764792343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53205512323647222353056457 39904134242735416764792343)
    ·
      refine ⟨59856201364103125147188515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39904134242735416764792343 59856201364103125147188515)
      ·
        refine ⟨89784302046154687720782773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59856201364103125147188515 89784302046154687720782773)
        ·
          refine ⟨8417278316827001973823385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89784302046154687720782773 8417278316827001973823385)
          ·
            refine ⟨6312958737620251480367539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8417278316827001973823385 6312958737620251480367539)
            ·
              refine ⟨9469438106430377220551309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312958737620251480367539 9469438106430377220551309)
              ·
                refine ⟨3551039289911391457706741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9469438106430377220551309 3551039289911391457706741)
                ·
                  refine ⟨332909933429192949160007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3551039289911391457706741 332909933429192949160007)
                  ·
                    rfl

theorem cell23_5835058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_5835058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835058 prefixEnd_5835058 := by exact prefixLift 5835058
  have htrace : WordTrace (prefixWord ++ tailWord_5835058) baseStart_5835058 baseEnd_5835058 := by
    simpa [prefixWord, tailWord_5835058, baseEnd_5835058] using wordTrace_append hprefix tailTrace_5835058
  have hstable : (prefixWord ++ tailWord_5835058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835058).length < 2 ^ (prefixWord ++ tailWord_5835058).sum := by decide
  have hdescent : baseEnd_5835058 < baseStart_5835058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835087 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_5835087 : Nat := 118140960795 + 5835087 * 2 ^ 59
def prefixEnd_5835087 : Nat := 4983230072969 + 3 ^ 40 * 5835087 * 2
def baseEnd_5835087 : Nat := 2996204291801716928977429

theorem tailTrace_5835087 : CollatzResearch.WordTrace tailWord_5835087 prefixEnd_5835087 2996204291801716928977429 := by
  unfold tailWord_5835087
  simp only [CollatzResearch.WordTrace]
  refine ⟨212823107011483827365031515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141882071340989218243354343 212823107011483827365031515)
  ·
    refine ⟨319234660517225741047547273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212823107011483827365031515 319234660517225741047547273)
    ·
      refine ⟨239425995387919305785660455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319234660517225741047547273 239425995387919305785660455)
      ·
        refine ⟨359138993081878958678490683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239425995387919305785660455 359138993081878958678490683)
        ·
          refine ⟨538708489622818438017736025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359138993081878958678490683 538708489622818438017736025)
          ·
            refine ⟨404031367217113828513302019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538708489622818438017736025 404031367217113828513302019)
            ·
              refine ⟨606047050825670742769953029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404031367217113828513302019 606047050825670742769953029)
              ·
                refine ⟨113633822029813264269366193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606047050825670742769953029 113633822029813264269366193)
                ·
                  refine ⟨85225366522359948202024645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113633822029813264269366193 85225366522359948202024645)
                  ·
                    refine ⟨15979756222942490287879621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85225366522359948202024645 15979756222942490287879621)
                    ·
                      refine ⟨2996204291801716928977429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15979756222942490287879621 2996204291801716928977429)
                      ·
                        rfl

theorem cell23_5835087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_5835087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835087 prefixEnd_5835087 := by exact prefixLift 5835087
  have htrace : WordTrace (prefixWord ++ tailWord_5835087) baseStart_5835087 baseEnd_5835087 := by
    simpa [prefixWord, tailWord_5835087, baseEnd_5835087] using wordTrace_append hprefix tailTrace_5835087
  have hstable : (prefixWord ++ tailWord_5835087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835087).length < 2 ^ (prefixWord ++ tailWord_5835087).sum := by decide
  have hdescent : baseEnd_5835087 < baseStart_5835087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835111 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_5835111 : Nat := 118140960795 + 5835111 * 2 ^ 59
def prefixEnd_5835111 : Nat := 4983230072969 + 3 ^ 40 * 5835111 * 2
def baseEnd_5835111 : Nat := 2996216615337424835077319

theorem tailTrace_5835111 : CollatzResearch.WordTrace tailWord_5835111 prefixEnd_5835111 2996216615337424835077319 := by
  unfold tailWord_5835111
  simp only [CollatzResearch.WordTrace]
  refine ⟨212823982363396879463905187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141882654908931252975936791 212823982363396879463905187)
  ·
    refine ⟨319235973545095319195857781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212823982363396879463905187 319235973545095319195857781)
    ·
      refine ⟨29928372519852686174611667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319235973545095319195857781 29928372519852686174611667)
      ·
        refine ⟨44892558779779029261917501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29928372519852686174611667 44892558779779029261917501)
        ·
          refine ⟨16834709542417135973219063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44892558779779029261917501 16834709542417135973219063)
          ·
            refine ⟨25252064313625703959828595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16834709542417135973219063 25252064313625703959828595)
            ·
              refine ⟨37878096470438555939742893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25252064313625703959828595 37878096470438555939742893)
              ·
                refine ⟨14204286176414458477403585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37878096470438555939742893 14204286176414458477403585)
                ·
                  refine ⟨10653214632310843858052689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14204286176414458477403585 10653214632310843858052689)
                  ·
                    refine ⟨7989910974233132893539517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10653214632310843858052689 7989910974233132893539517)
                    ·
                      refine ⟨2996216615337424835077319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989910974233132893539517 2996216615337424835077319)
                      ·
                        rfl

theorem cell23_5835111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_5835111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835111 prefixEnd_5835111 := by exact prefixLift 5835111
  have htrace : WordTrace (prefixWord ++ tailWord_5835111) baseStart_5835111 baseEnd_5835111 := by
    simpa [prefixWord, tailWord_5835111, baseEnd_5835111] using wordTrace_append hprefix tailTrace_5835111
  have hstable : (prefixWord ++ tailWord_5835111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835111).length < 2 ^ (prefixWord ++ tailWord_5835111).sum := by decide
  have hdescent : baseEnd_5835111 < baseStart_5835111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835141 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_5835141 : Nat := 118140960795 + 5835141 * 2 ^ 59
def prefixEnd_5835141 : Nat := 4983230072969 + 3 ^ 40 * 5835141 * 2
def baseEnd_5835141 : Nat := 2996232019757059717702181

theorem tailTrace_5835141 : CollatzResearch.WordTrace tailWord_5835141 prefixEnd_5835141 2996232019757059717702181 := by
  unfold tailWord_5835141
  simp only [CollatzResearch.WordTrace]
  refine ⟨212825076553288194587497277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141883384368858796391664851 212825076553288194587497277)
  ·
    refine ⟨79809403707483072970311479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212825076553288194587497277 79809403707483072970311479)
    ·
      refine ⟨119714105561224609455467219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79809403707483072970311479 119714105561224609455467219)
      ·
        refine ⟨179571158341836914183200829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119714105561224609455467219 179571158341836914183200829)
        ·
          refine ⟨67339184378188842818700311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179571158341836914183200829 67339184378188842818700311)
          ·
            refine ⟨101008776567283264228050467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67339184378188842818700311 101008776567283264228050467)
            ·
              refine ⟨151513164850924896342075701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101008776567283264228050467 151513164850924896342075701)
              ·
                refine ⟨14204359204774209032069597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151513164850924896342075701 14204359204774209032069597)
                ·
                  refine ⟨5326634701790328387026099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14204359204774209032069597 5326634701790328387026099)
                  ·
                    refine ⟨7989952052685492580539149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326634701790328387026099 7989952052685492580539149)
                    ·
                      refine ⟨2996232019757059717702181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989952052685492580539149 2996232019757059717702181)
                      ·
                        rfl

theorem cell23_5835141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_5835141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835141 prefixEnd_5835141 := by exact prefixLift 5835141
  have htrace : WordTrace (prefixWord ++ tailWord_5835141) baseStart_5835141 baseEnd_5835141 := by
    simpa [prefixWord, tailWord_5835141, baseEnd_5835141] using wordTrace_append hprefix tailTrace_5835141
  have hstable : (prefixWord ++ tailWord_5835141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835141).length < 2 ^ (prefixWord ++ tailWord_5835141).sum := by decide
  have hdescent : baseEnd_5835141 < baseStart_5835141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835144 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_5835144 : Nat := 118140960795 + 5835144 * 2 ^ 59
def prefixEnd_5835144 : Nat := 4983230072969 + 3 ^ 40 * 5835144 * 2
def baseEnd_5835144 : Nat := 998744520066341068654889

theorem tailTrace_5835144 : CollatzResearch.WordTrace tailWord_5835144 prefixEnd_5835144 998744520066341068654889 := by
  unfold tailWord_5835144
  simp only [CollatzResearch.WordTrace]
  refine ⟨106412592986138663049928243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141883457314851550733237657 106412592986138663049928243)
  ·
    refine ⟨159618889479207994574892365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106412592986138663049928243 159618889479207994574892365)
    ·
      refine ⟨59857083554702997965584637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159618889479207994574892365 59857083554702997965584637)
      ·
        refine ⟨22446406333013624237094239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59857083554702997965584637 22446406333013624237094239)
        ·
          refine ⟨33669609499520436355641359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446406333013624237094239 33669609499520436355641359)
          ·
            refine ⟨50504414249280654533462039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33669609499520436355641359 50504414249280654533462039)
            ·
              refine ⟨75756621373920981800193059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50504414249280654533462039 75756621373920981800193059)
              ·
                refine ⟨113634932060881472700289589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75756621373920981800193059 113634932060881472700289589)
                ·
                  refine ⟨10653274880707638065652149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113634932060881472700289589 10653274880707638065652149)
                  ·
                    refine ⟨998744520066341068654889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10653274880707638065652149 998744520066341068654889)
                    ·
                      rfl

theorem cell23_5835144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_5835144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835144 prefixEnd_5835144 := by exact prefixLift 5835144
  have htrace : WordTrace (prefixWord ++ tailWord_5835144) baseStart_5835144 baseEnd_5835144 := by
    simpa [prefixWord, tailWord_5835144, baseEnd_5835144] using wordTrace_append hprefix tailTrace_5835144
  have hstable : (prefixWord ++ tailWord_5835144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835144).length < 2 ^ (prefixWord ++ tailWord_5835144).sum := by decide
  have hdescent : baseEnd_5835144 < baseStart_5835144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835168 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2]
def baseStart_5835168 : Nat := 118140960795 + 5835168 * 2 ^ 59
def prefixEnd_5835168 : Nat := 4983230072969 + 3 ^ 40 * 5835168 * 2
def baseEnd_5835168 : Nat := 2996245883734731112064557

theorem tailTrace_5835168 : CollatzResearch.WordTrace tailWord_5835168 prefixEnd_5835168 2996245883734731112064557 := by
  unfold tailWord_5835168
  simp only [CollatzResearch.WordTrace]
  refine ⟨106413030662095189099365079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141884040882793585465820105 106413030662095189099365079)
  ·
    refine ⟨159619545993142783649047619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106413030662095189099365079 159619545993142783649047619)
    ·
      refine ⟨239429318989714175473571429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159619545993142783649047619 239429318989714175473571429)
      ·
        refine ⟨44892997310571407901294643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239429318989714175473571429 44892997310571407901294643)
        ·
          refine ⟨67339495965857111851941965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44892997310571407901294643 67339495965857111851941965)
          ·
            refine ⟨25252310987196416944478237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67339495965857111851941965 25252310987196416944478237)
            ·
              refine ⟨9469616620198656354179339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25252310987196416944478237 9469616620198656354179339)
              ·
                refine ⟨14204424930297984531269009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9469616620198656354179339 14204424930297984531269009)
                ·
                  refine ⟨10653318697723488398451757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14204424930297984531269009 10653318697723488398451757)
                  ·
                    refine ⟨3994994511646308149419409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10653318697723488398451757 3994994511646308149419409)
                    ·
                      refine ⟨2996245883734731112064557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3994994511646308149419409 2996245883734731112064557)
                      ·
                        rfl

theorem cell23_5835168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_5835168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835168 prefixEnd_5835168 := by exact prefixLift 5835168
  have htrace : WordTrace (prefixWord ++ tailWord_5835168) baseStart_5835168 baseEnd_5835168 := by
    simpa [prefixWord, tailWord_5835168, baseEnd_5835168] using wordTrace_append hprefix tailTrace_5835168
  have hstable : (prefixWord ++ tailWord_5835168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835168).length < 2 ^ (prefixWord ++ tailWord_5835168).sum := by decide
  have hdescent : baseEnd_5835168 < baseStart_5835168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835175 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5835175 : Nat := 118140960795 + 5835175 * 2 ^ 59
def prefixEnd_5835175 : Nat := 4983230072969 + 3 ^ 40 * 5835175 * 2
def baseEnd_5835175 : Nat := 2996249478099312584677025

theorem tailTrace_5835175 : CollatzResearch.WordTrace tailWord_5835175 prefixEnd_5835175 2996249478099312584677025 := by
  unfold tailWord_5835175
  simp only [CollatzResearch.WordTrace]
  refine ⟨212826316635165018394234979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141884211090110012262823319 212826316635165018394234979)
  ·
    refine ⟨319239474952747527591352469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212826316635165018394234979 319239474952747527591352469)
    ·
      refine ⟨14964350388410040355844647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 319239474952747527591352469 14964350388410040355844647)
      ·
        refine ⟨22446525582615060533766971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964350388410040355844647 22446525582615060533766971)
        ·
          refine ⟨33669788373922590800650457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446525582615060533766971 33669788373922590800650457)
          ·
            refine ⟨25252341280441943100487843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33669788373922590800650457 25252341280441943100487843)
            ·
              refine ⟨37878511920662914650731765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25252341280441943100487843 37878511920662914650731765)
              ·
                refine ⟨3551110492562148248506103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37878511920662914650731765 3551110492562148248506103)
                ·
                  refine ⟨5326665738843222372759155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551110492562148248506103 5326665738843222372759155)
                  ·
                    refine ⟨7989998608264833559138733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326665738843222372759155 7989998608264833559138733)
                    ·
                      refine ⟨2996249478099312584677025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7989998608264833559138733 2996249478099312584677025)
                      ·
                        rfl

theorem cell23_5835175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5835175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835175 prefixEnd_5835175 := by exact prefixLift 5835175
  have htrace : WordTrace (prefixWord ++ tailWord_5835175) baseStart_5835175 baseEnd_5835175 := by
    simpa [prefixWord, tailWord_5835175, baseEnd_5835175] using wordTrace_append hprefix tailTrace_5835175
  have hstable : (prefixWord ++ tailWord_5835175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835175).length < 2 ^ (prefixWord ++ tailWord_5835175).sum := by decide
  have hdescent : baseEnd_5835175 < baseStart_5835175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835191 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 4, 4]
def baseStart_5835191 : Nat := 118140960795 + 5835191 * 2 ^ 59
def prefixEnd_5835191 : Nat := 4983230072969 + 3 ^ 40 * 5835191 * 2
def baseEnd_5835191 : Nat := 998752564596594840692317

theorem tailTrace_5835191 : CollatzResearch.WordTrace tailWord_5835191 prefixEnd_5835191 998752564596594840692317 := by
  unfold tailWord_5835191
  simp only [CollatzResearch.WordTrace]
  refine ⟨212826900203107053126817427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141884600135404702084544951 212826900203107053126817427)
  ·
    refine ⟨319240350304660579690226141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212826900203107053126817427 319240350304660579690226141)
    ·
      refine ⟨119715131364247717383834803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319240350304660579690226141 119715131364247717383834803)
      ·
        refine ⟨179572697046371576075752205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119715131364247717383834803 179572697046371576075752205)
        ·
          refine ⟨67339761392389341028407077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179572697046371576075752205 67339761392389341028407077)
          ·
            refine ⟨12626205261073001442826327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67339761392389341028407077 12626205261073001442826327)
            ·
              refine ⟨18939307891609502164239491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12626205261073001442826327 18939307891609502164239491)
              ·
                refine ⟨28408961837414253246359237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18939307891609502164239491 28408961837414253246359237)
                ·
                  refine ⟨5326680344515172483692357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28408961837414253246359237 5326680344515172483692357)
                  ·
                    refine ⟨998752564596594840692317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5326680344515172483692357 998752564596594840692317)
                    ·
                      rfl

theorem cell23_5835191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_5835191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835191 prefixEnd_5835191 := by exact prefixLift 5835191
  have htrace : WordTrace (prefixWord ++ tailWord_5835191) baseStart_5835191 baseEnd_5835191 := by
    simpa [prefixWord, tailWord_5835191, baseEnd_5835191] using wordTrace_append hprefix tailTrace_5835191
  have hstable : (prefixWord ++ tailWord_5835191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835191).length < 2 ^ (prefixWord ++ tailWord_5835191).sum := by decide
  have hdescent : baseEnd_5835191 < baseStart_5835191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835194 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_5835194 : Nat := 118140960795 + 5835194 * 2 ^ 59
def prefixEnd_5835194 : Nat := 4983230072969 + 3 ^ 40 * 5835194 * 2
def baseEnd_5835194 : Nat := 2996259234231748010339437

theorem tailTrace_5835194 : CollatzResearch.WordTrace tailWord_5835194 prefixEnd_5835194 2996259234231748010339437 := by
  unfold tailWord_5835194
  simp only [CollatzResearch.WordTrace]
  refine ⟨53206752405524046159794159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141884673081397456426117757 53206752405524046159794159)
  ·
    refine ⟨79810128608286069239691239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53206752405524046159794159 79810128608286069239691239)
    ·
      refine ⟨119715192912429103859536859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79810128608286069239691239 119715192912429103859536859)
      ·
        refine ⟨179572789368643655789305289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119715192912429103859536859 179572789368643655789305289)
        ·
          refine ⟨134679592026482741841978967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179572789368643655789305289 134679592026482741841978967)
          ·
            refine ⟨202019388039724112762968451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134679592026482741841978967 202019388039724112762968451)
            ·
              refine ⟨303029082059586169144452677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202019388039724112762968451 303029082059586169144452677)
              ·
                refine ⟨56817952886172406714584877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303029082059586169144452677 56817952886172406714584877)
                ·
                  refine ⟨21306732332314652517969329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56817952886172406714584877 21306732332314652517969329)
                  ·
                    refine ⟨15980049249235989388476997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21306732332314652517969329 15980049249235989388476997)
                    ·
                      refine ⟨2996259234231748010339437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15980049249235989388476997 2996259234231748010339437)
                      ·
                        rfl

theorem cell23_5835194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_5835194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835194 prefixEnd_5835194 := by exact prefixLift 5835194
  have htrace : WordTrace (prefixWord ++ tailWord_5835194) baseStart_5835194 baseEnd_5835194 := by
    simpa [prefixWord, tailWord_5835194, baseEnd_5835194] using wordTrace_append hprefix tailTrace_5835194
  have hstable : (prefixWord ++ tailWord_5835194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835194).length < 2 ^ (prefixWord ++ tailWord_5835194).sum := by decide
  have hdescent : baseEnd_5835194 < baseStart_5835194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835221 : List Nat := [1, 3, 2, 3, 1, 2, 4, 7]
def baseStart_5835221 : Nat := 118140960795 + 5835221 * 2 ^ 59
def prefixEnd_5835221 : Nat := 4983230072969 + 3 ^ 40 * 5835221 * 2
def baseEnd_5835221 : Nat := 110973077711459977951919

theorem tailTrace_5835221 : CollatzResearch.WordTrace tailWord_5835221 prefixEnd_5835221 110973077711459977951919 := by
  unfold tailWord_5835221
  simp only [CollatzResearch.WordTrace]
  refine ⟨212827994392998368250409517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141885329595332245500273011 212827994392998368250409517)
  ·
    refine ⟨79810497897374388093903569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212827994392998368250409517 79810497897374388093903569)
    ·
      refine ⟨59857873423030791070427677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79810497897374388093903569 59857873423030791070427677)
      ·
        refine ⟨22446702533636546651410379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59857873423030791070427677 22446702533636546651410379)
        ·
          refine ⟨33670053800454819977115569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446702533636546651410379 33670053800454819977115569)
          ·
            refine ⟨25252540350341114982836677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33670053800454819977115569 25252540350341114982836677)
            ·
              refine ⟨4734851315688959059281877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25252540350341114982836677 4734851315688959059281877)
              ·
                refine ⟨110973077711459977951919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4734851315688959059281877 110973077711459977951919)
                ·
                  rfl

theorem cell23_5835221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 7].length) (baseStart_5835221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835221 prefixEnd_5835221 := by exact prefixLift 5835221
  have htrace : WordTrace (prefixWord ++ tailWord_5835221) baseStart_5835221 baseEnd_5835221 := by
    simpa [prefixWord, tailWord_5835221, baseEnd_5835221] using wordTrace_append hprefix tailTrace_5835221
  have hstable : (prefixWord ++ tailWord_5835221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835221).length < 2 ^ (prefixWord ++ tailWord_5835221).sum := by decide
  have hdescent : baseEnd_5835221 < baseStart_5835221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835244 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_5835244 : Nat := 118140960795 + 5835244 * 2 ^ 59
def prefixEnd_5835244 : Nat := 4983230072969 + 3 ^ 40 * 5835244 * 2
def baseEnd_5835244 : Nat := 2996284908264472814714207

theorem tailTrace_5835244 : CollatzResearch.WordTrace tailWord_5835244 prefixEnd_5835244 2996284908264472814714207 := by
  unfold tailWord_5835244
  simp only [CollatzResearch.WordTrace]
  refine ⟨106414416635957521589248393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141885888847943362118997857 106414416635957521589248393)
  ·
    refine ⟨79810812476968141191936295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106414416635957521589248393 79810812476968141191936295)
    ·
      refine ⟨119716218715452211787904443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79810812476968141191936295 119716218715452211787904443)
      ·
        refine ⟨179574328073178317681856665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119716218715452211787904443 179574328073178317681856665)
        ·
          refine ⟨134680746054883738261392499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179574328073178317681856665 134680746054883738261392499)
          ·
            refine ⟨202021119082325607392088749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134680746054883738261392499 202021119082325607392088749)
            ·
              refine ⟨75757919655872102772033281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202021119082325607392088749 75757919655872102772033281)
              ·
                refine ⟨56818439741904077079024961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75757919655872102772033281 56818439741904077079024961)
                ·
                  refine ⟨42613829806428057809268721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56818439741904077079024961 42613829806428057809268721)
                  ·
                    refine ⟨31960372354821043356951541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42613829806428057809268721 31960372354821043356951541)
                    ·
                      refine ⟨2996284908264472814714207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31960372354821043356951541 2996284908264472814714207)
                      ·
                        rfl

theorem cell23_5835244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_5835244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835244 prefixEnd_5835244 := by exact prefixLift 5835244
  have htrace : WordTrace (prefixWord ++ tailWord_5835244) baseStart_5835244 baseEnd_5835244 := by
    simpa [prefixWord, tailWord_5835244, baseEnd_5835244] using wordTrace_append hprefix tailTrace_5835244
  have hstable : (prefixWord ++ tailWord_5835244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835244).length < 2 ^ (prefixWord ++ tailWord_5835244).sum := by decide
  have hdescent : baseEnd_5835244 < baseStart_5835244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835248 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3]
def baseStart_5835248 : Nat := 118140960795 + 5835248 * 2 ^ 59
def prefixEnd_5835248 : Nat := 4983230072969 + 3 ^ 40 * 5835248 * 2
def baseEnd_5835248 : Nat := 2996286962187090799064189

theorem tailTrace_5835248 : CollatzResearch.WordTrace tailWord_5835248 prefixEnd_5835248 2996286962187090799064189 := by
  unfold tailWord_5835248
  simp only [CollatzResearch.WordTrace]
  refine ⟨106414489581950275930821199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141885986109267034574428265 106414489581950275930821199)
  ·
    refine ⟨159621734372925413896231799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106414489581950275930821199 159621734372925413896231799)
    ·
      refine ⟨239432601559388120844347699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159621734372925413896231799 239432601559388120844347699)
      ·
        refine ⟨359148902339082181266521549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239432601559388120844347699 359148902339082181266521549)
        ·
          refine ⟨134680838377155817974945581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359148902339082181266521549 134680838377155817974945581)
          ·
            refine ⟨50505314391433431740604593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134680838377155817974945581 50505314391433431740604593)
            ·
              refine ⟨37878985793575073805453445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50505314391433431740604593 37878985793575073805453445)
              ·
                refine ⟨7102309836295326338522521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37878985793575073805453445 7102309836295326338522521)
                ·
                  refine ⟨5326732377221494753891891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102309836295326338522521 5326732377221494753891891)
                  ·
                    refine ⟨7990098565832242130837837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326732377221494753891891 7990098565832242130837837)
                    ·
                      refine ⟨2996286962187090799064189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990098565832242130837837 2996286962187090799064189)
                      ·
                        rfl

theorem cell23_5835248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_5835248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835248 prefixEnd_5835248 := by exact prefixLift 5835248
  have htrace : WordTrace (prefixWord ++ tailWord_5835248) baseStart_5835248 baseEnd_5835248 := by
    simpa [prefixWord, tailWord_5835248, baseEnd_5835248] using wordTrace_append hprefix tailTrace_5835248
  have hstable : (prefixWord ++ tailWord_5835248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835248).length < 2 ^ (prefixWord ++ tailWord_5835248).sum := by decide
  have hdescent : baseEnd_5835248 < baseStart_5835248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835265 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_5835265 : Nat := 118140960795 + 5835265 * 2 ^ 59
def prefixEnd_5835265 : Nat := 4983230072969 + 3 ^ 40 * 5835265 * 2
def baseEnd_5835265 : Nat := 2996295691358217232551611

theorem tailTrace_5835265 : CollatzResearch.WordTrace tailWord_5835265 prefixEnd_5835265 2996295691358217232551611 := by
  unfold tailWord_5835265
  simp only [CollatzResearch.WordTrace]
  refine ⟨212829599204838963765011249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141886399469892642510007499 212829599204838963765011249)
  ·
    refine ⟨159622199403629222823758437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212829599204838963765011249 159622199403629222823758437)
    ·
      refine ⟨29929162388180479279454707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159622199403629222823758437 29929162388180479279454707)
      ·
        refine ⟨44893743582270718919182061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29929162388180479279454707 44893743582270718919182061)
        ·
          refine ⟨16835153843351519594693273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44893743582270718919182061 16835153843351519594693273)
          ·
            refine ⟨12626365382513639696019955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16835153843351519594693273 12626365382513639696019955)
            ·
              refine ⟨18939548073770459544029933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12626365382513639696019955 18939548073770459544029933)
              ·
                refine ⟨7102330527663922329011225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18939548073770459544029933 7102330527663922329011225)
                ·
                  refine ⟨5326747895747941746758419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102330527663922329011225 5326747895747941746758419)
                  ·
                    refine ⟨7990121843621912620137629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326747895747941746758419 7990121843621912620137629)
                    ·
                      refine ⟨2996295691358217232551611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990121843621912620137629 2996295691358217232551611)
                      ·
                        rfl

theorem cell23_5835265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_5835265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835265 prefixEnd_5835265 := by exact prefixLift 5835265
  have htrace : WordTrace (prefixWord ++ tailWord_5835265) baseStart_5835265 baseEnd_5835265 := by
    simpa [prefixWord, tailWord_5835265, baseEnd_5835265] using wordTrace_append hprefix tailTrace_5835265
  have hstable : (prefixWord ++ tailWord_5835265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835265).length < 2 ^ (prefixWord ++ tailWord_5835265).sum := by decide
  have hdescent : baseEnd_5835265 < baseStart_5835265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835275 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 1, 3, 2]
def baseStart_5835275 : Nat := 118140960795 + 5835275 * 2 ^ 59
def prefixEnd_5835275 : Nat := 4983230072969 + 3 ^ 40 * 5835275 * 2
def baseEnd_5835275 : Nat := 2996300826164762193426565

theorem tailTrace_5835275 : CollatzResearch.WordTrace tailWord_5835275 prefixEnd_5835275 2996300826164762193426565 := by
  unfold tailWord_5835275
  simp only [CollatzResearch.WordTrace]
  refine ⟨212829963934802735472875279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141886642623201823648583519 212829963934802735472875279)
  ·
    refine ⟨319244945902204103209312919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212829963934802735472875279 319244945902204103209312919)
    ·
      refine ⟨478867418853306154813969379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319244945902204103209312919 478867418853306154813969379)
      ·
        refine ⟨718301128279959232220954069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478867418853306154813969379 718301128279959232220954069)
        ·
          refine ⟨16835182694061544505178611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 718301128279959232220954069 16835182694061544505178611)
          ·
            refine ⟨25252774041092316757767917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835182694061544505178611 25252774041092316757767917)
            ·
              refine ⟨9469790265409618784162969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25252774041092316757767917 9469790265409618784162969)
              ·
                refine ⟨7102342699057214088122227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9469790265409618784162969 7102342699057214088122227)
                ·
                  refine ⟨10653514048585821132183341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7102342699057214088122227 10653514048585821132183341)
                  ·
                    refine ⟨3995067768219682924568753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10653514048585821132183341 3995067768219682924568753)
                    ·
                      refine ⟨2996300826164762193426565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995067768219682924568753 2996300826164762193426565)
                      ·
                        rfl

theorem cell23_5835275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 3, 2].length) (baseStart_5835275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835275 prefixEnd_5835275 := by exact prefixLift 5835275
  have htrace : WordTrace (prefixWord ++ tailWord_5835275) baseStart_5835275 baseEnd_5835275 := by
    simpa [prefixWord, tailWord_5835275, baseEnd_5835275] using wordTrace_append hprefix tailTrace_5835275
  have hstable : (prefixWord ++ tailWord_5835275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835275).length < 2 ^ (prefixWord ++ tailWord_5835275).sum := by decide
  have hdescent : baseEnd_5835275 < baseStart_5835275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835288 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_5835288 : Nat := 118140960795 + 5835288 * 2 ^ 59
def prefixEnd_5835288 : Nat := 4983230072969 + 3 ^ 40 * 5835288 * 2
def baseEnd_5835288 : Nat := 2996307501413270642564005

theorem tailTrace_5835288 : CollatzResearch.WordTrace tailWord_5835288 prefixEnd_5835288 2996307501413270642564005 := by
  unfold tailWord_5835288
  simp only [CollatzResearch.WordTrace]
  refine ⟨106415219041877819346549259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141886958722503759128732345 106415219041877819346549259)
  ·
    refine ⟨159622828562816729019823889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106415219041877819346549259 159622828562816729019823889)
    ·
      refine ⟨119717121422112546764867917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159622828562816729019823889 119717121422112546764867917)
      ·
        refine ⟨44893920533292205036825469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119717121422112546764867917 44893920533292205036825469)
        ·
          refine ⟨16835220199984576888809551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44893920533292205036825469 16835220199984576888809551)
          ·
            refine ⟨25252830299976865333214327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835220199984576888809551 25252830299976865333214327)
            ·
              refine ⟨37879245449965297999821491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25252830299976865333214327 37879245449965297999821491)
              ·
                refine ⟨56818868174947946999732237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37879245449965297999821491 56818868174947946999732237)
                ·
                  refine ⟨21307075565605480124899589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56818868174947946999732237 21307075565605480124899589)
                  ·
                    refine ⟨3995076668551027523418673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21307075565605480124899589 3995076668551027523418673)
                    ·
                      refine ⟨2996307501413270642564005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995076668551027523418673 2996307501413270642564005)
                      ·
                        rfl

theorem cell23_5835288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_5835288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835288 prefixEnd_5835288 := by exact prefixLift 5835288
  have htrace : WordTrace (prefixWord ++ tailWord_5835288) baseStart_5835288 baseEnd_5835288 := by
    simpa [prefixWord, tailWord_5835288, baseEnd_5835288] using wordTrace_append hprefix tailTrace_5835288
  have hstable : (prefixWord ++ tailWord_5835288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835288).length < 2 ^ (prefixWord ++ tailWord_5835288).sum := by decide
  have hdescent : baseEnd_5835288 < baseStart_5835288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835292 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5835292 : Nat := 118140960795 + 5835292 * 2 ^ 59
def prefixEnd_5835292 : Nat := 4983230072969 + 3 ^ 40 * 5835292 * 2
def baseEnd_5835292 : Nat := 2996309555335888626913987

theorem tailTrace_5835292 : CollatzResearch.WordTrace tailWord_5835292 prefixEnd_5835292 2996309555335888626913987 := by
  unfold tailWord_5835292
  simp only [CollatzResearch.WordTrace]
  refine ⟨106415291987870573688122065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141887055983827431584162753 106415291987870573688122065)
  ·
    refine ⟨79811468990902930266091549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106415291987870573688122065 79811468990902930266091549)
    ·
      refine ⟨29929300871588598849784331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79811468990902930266091549 29929300871588598849784331)
      ·
        refine ⟨44893951307382898274676497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29929300871588598849784331 44893951307382898274676497)
        ·
          refine ⟨33670463480537173706007373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44893951307382898274676497 33670463480537173706007373)
          ·
            refine ⟨12626423805201440139752765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33670463480537173706007373 12626423805201440139752765)
            ·
              refine ⟨4734908926950540052407287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12626423805201440139752765 4734908926950540052407287)
              ·
                refine ⟨7102363390425810078610931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734908926950540052407287 7102363390425810078610931)
                ·
                  refine ⟨10653545085638715117916397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7102363390425810078610931 10653545085638715117916397)
                  ·
                    refine ⟨3995079407114518169218649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10653545085638715117916397 3995079407114518169218649)
                    ·
                      refine ⟨2996309555335888626913987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995079407114518169218649 2996309555335888626913987)
                      ·
                        rfl

theorem cell23_5835292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5835292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835292 prefixEnd_5835292 := by exact prefixLift 5835292
  have htrace : WordTrace (prefixWord ++ tailWord_5835292) baseStart_5835292 baseEnd_5835292 := by
    simpa [prefixWord, tailWord_5835292, baseEnd_5835292] using wordTrace_append hprefix tailTrace_5835292
  have hstable : (prefixWord ++ tailWord_5835292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835292).length < 2 ^ (prefixWord ++ tailWord_5835292).sum := by decide
  have hdescent : baseEnd_5835292 < baseStart_5835292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835318 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5835318 : Nat := 118140960795 + 5835318 * 2 ^ 59
def prefixEnd_5835318 : Nat := 4983230072969 + 3 ^ 40 * 5835318 * 2
def baseEnd_5835318 : Nat := 2996322905832905525188867

theorem tailTrace_5835318 : CollatzResearch.WordTrace tailWord_5835318 prefixEnd_5835318 2996322905832905525188867 := by
  unfold tailWord_5835318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301970767102934613543163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141887688182431302544460405 13301970767102934613543163)
  ·
    refine ⟨19952956150654401920314745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13301970767102934613543163 19952956150654401920314745)
    ·
      refine ⟨14964717112990801440236059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19952956150654401920314745 14964717112990801440236059)
      ·
        refine ⟨22447075669486202160354089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964717112990801440236059 22447075669486202160354089)
        ·
          refine ⟨16835306752114651620265567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22447075669486202160354089 16835306752114651620265567)
          ·
            refine ⟨25252960128171977430398351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835306752114651620265567 25252960128171977430398351)
            ·
              refine ⟨37879440192257966145597527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25252960128171977430398351 37879440192257966145597527)
              ·
                refine ⟨56819160288386949218396291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37879440192257966145597527 56819160288386949218396291)
                ·
                  refine ⟨85228740432580423827594437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56819160288386949218396291 85228740432580423827594437)
                  ·
                    refine ⟨15980388831108829467673957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85228740432580423827594437 15980388831108829467673957)
                    ·
                      refine ⟨2996322905832905525188867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15980388831108829467673957 2996322905832905525188867)
                      ·
                        rfl

theorem cell23_5835318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5835318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835318 prefixEnd_5835318 := by exact prefixLift 5835318
  have htrace : WordTrace (prefixWord ++ tailWord_5835318) baseStart_5835318 baseEnd_5835318 := by
    simpa [prefixWord, tailWord_5835318, baseEnd_5835318] using wordTrace_append hprefix tailTrace_5835318
  have hstable : (prefixWord ++ tailWord_5835318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835318).length < 2 ^ (prefixWord ++ tailWord_5835318).sum := by decide
  have hdescent : baseEnd_5835318 < baseStart_5835318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835356 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5835356 : Nat := 118140960795 + 5835356 * 2 ^ 59
def prefixEnd_5835356 : Nat := 4983230072969 + 3 ^ 40 * 5835356 * 2
def baseEnd_5835356 : Nat := 2996342418097776376513693

theorem tailTrace_5835356 : CollatzResearch.WordTrace tailWord_5835356 prefixEnd_5835356 2996342418097776376513693 := by
  unfold tailWord_5835356
  simp only [CollatzResearch.WordTrace]
  refine ⟨106416459123754643153286961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141888612165006190871049281 106416459123754643153286961)
  ·
    refine ⟨79812344342815982364965221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106416459123754643153286961 79812344342815982364965221)
    ·
      refine ⟨14964814564277996693430979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79812344342815982364965221 14964814564277996693430979)
      ·
        refine ⟨22447221846416995040146469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964814564277996693430979 22447221846416995040146469)
        ·
          refine ⟨4208854096203186570027463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22447221846416995040146469 4208854096203186570027463)
          ·
            refine ⟨6313281144304779855041195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208854096203186570027463 6313281144304779855041195)
            ·
              refine ⟨9469921716457169782561793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313281144304779855041195 9469921716457169782561793)
              ·
                refine ⟨7102441287342877336921345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9469921716457169782561793 7102441287342877336921345)
                ·
                  refine ⟨5326830965507158002691009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102441287342877336921345 5326830965507158002691009)
                  ·
                    refine ⟨3995123224130368502018257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326830965507158002691009 3995123224130368502018257)
                    ·
                      refine ⟨2996342418097776376513693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995123224130368502018257 2996342418097776376513693)
                      ·
                        rfl

theorem cell23_5835356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5835356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835356 prefixEnd_5835356 := by exact prefixLift 5835356
  have htrace : WordTrace (prefixWord ++ tailWord_5835356) baseStart_5835356 baseEnd_5835356 := by
    simpa [prefixWord, tailWord_5835356, baseEnd_5835356] using wordTrace_append hprefix tailTrace_5835356
  have hstable : (prefixWord ++ tailWord_5835356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835356).length < 2 ^ (prefixWord ++ tailWord_5835356).sum := by decide
  have hdescent : baseEnd_5835356 < baseStart_5835356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835388 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_5835388 : Nat := 118140960795 + 5835388 * 2 ^ 59
def prefixEnd_5835388 : Nat := 4983230072969 + 3 ^ 40 * 5835388 * 2
def baseEnd_5835388 : Nat := 998786283159573417104515

theorem tailTrace_5835388 : CollatzResearch.WordTrace tailWord_5835388 prefixEnd_5835388 998786283159573417104515 := by
  unfold tailWord_5835388
  simp only [CollatzResearch.WordTrace]
  refine ⟨106417042691696677885869409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141889390255595570514492545 106417042691696677885869409)
  ·
    refine ⟨79812782018772508414402057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106417042691696677885869409 79812782018772508414402057)
    ·
      refine ⟨59859586514079381310801543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79812782018772508414402057 59859586514079381310801543)
      ·
        refine ⟨89789379771119071966202315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59859586514079381310801543 89789379771119071966202315)
        ·
          refine ⟨134684069656678607949303473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89789379771119071966202315 134684069656678607949303473)
          ·
            refine ⟨101013052242508955961977605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134684069656678607949303473 101013052242508955961977605)
            ·
              refine ⟨18939947295470429242870801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101013052242508955961977605 18939947295470429242870801)
              ·
                refine ⟨14204960471602821932153101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18939947295470429242870801 14204960471602821932153101)
                ·
                  refine ⟨5326860176851058224557413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14204960471602821932153101 5326860176851058224557413)
                  ·
                    refine ⟨998786283159573417104515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5326860176851058224557413 998786283159573417104515)
                    ·
                      rfl

theorem cell23_5835388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_5835388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835388 prefixEnd_5835388 := by exact prefixLift 5835388
  have htrace : WordTrace (prefixWord ++ tailWord_5835388) baseStart_5835388 baseEnd_5835388 := by
    simpa [prefixWord, tailWord_5835388, baseEnd_5835388] using wordTrace_append hprefix tailTrace_5835388
  have hstable : (prefixWord ++ tailWord_5835388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835388).length < 2 ^ (prefixWord ++ tailWord_5835388).sum := by decide
  have hdescent : baseEnd_5835388 < baseStart_5835388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835411 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3]
def baseStart_5835411 : Nat := 118140960795 + 5835411 * 2 ^ 59
def prefixEnd_5835411 : Nat := 4983230072969 + 3 ^ 40 * 5835411 * 2
def baseEnd_5835411 : Nat := 2996370659533773661325939

theorem tailTrace_5835411 : CollatzResearch.WordTrace tailWord_5835411 prefixEnd_5835411 2996370659533773661325939 := by
  unfold tailWord_5835411
  simp only [CollatzResearch.WordTrace]
  refine ⟨212834924262310030699826087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141889949508206687133217391 212834924262310030699826087)
  ·
    refine ⟨319252386393465046049739131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212834924262310030699826087 319252386393465046049739131)
    ·
      refine ⟨478878579590197569074608697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319252386393465046049739131 478878579590197569074608697)
      ·
        refine ⟨359158934692648176805956523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478878579590197569074608697 359158934692648176805956523)
        ·
          refine ⟨538738402038972265208934785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359158934692648176805956523 538738402038972265208934785)
          ·
            refine ⟨404053801529229198906701089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538738402038972265208934785 404053801529229198906701089)
            ·
              refine ⟨303040351146921899180025817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404053801529229198906701089 303040351146921899180025817)
              ·
                refine ⟨227280263360191424385019363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303040351146921899180025817 227280263360191424385019363)
                ·
                  refine ⟨340920395040287136577529045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227280263360191424385019363 340920395040287136577529045)
                  ·
                    refine ⟨7990321758756729763535837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 340920395040287136577529045 7990321758756729763535837)
                    ·
                      refine ⟨2996370659533773661325939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990321758756729763535837 2996370659533773661325939)
                      ·
                        rfl

theorem cell23_5835411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_5835411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835411 prefixEnd_5835411 := by exact prefixLift 5835411
  have htrace : WordTrace (prefixWord ++ tailWord_5835411) baseStart_5835411 baseEnd_5835411 := by
    simpa [prefixWord, tailWord_5835411, baseEnd_5835411] using wordTrace_append hprefix tailTrace_5835411
  have hstable : (prefixWord ++ tailWord_5835411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835411).length < 2 ^ (prefixWord ++ tailWord_5835411).sum := by decide
  have hdescent : baseEnd_5835411 < baseStart_5835411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835421 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5835421 : Nat := 118140960795 + 5835421 * 2 ^ 59
def prefixEnd_5835421 : Nat := 4983230072969 + 3 ^ 40 * 5835421 * 2
def baseEnd_5835421 : Nat := 2996375794340318622200893

theorem tailTrace_5835421 : CollatzResearch.WordTrace tailWord_5835421 prefixEnd_5835421 2996375794340318622200893 := by
  unfold tailWord_5835421
  simp only [CollatzResearch.WordTrace]
  refine ⟨212835288992273802407690117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141890192661515868271793411 212835288992273802407690117)
  ·
    refine ⟨39906616686051337951441897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212835288992273802407690117 39906616686051337951441897)
    ·
      refine ⟨29929962514538503463581423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39906616686051337951441897 29929962514538503463581423)
      ·
        refine ⟨44894943771807755195372135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29929962514538503463581423 44894943771807755195372135)
        ·
          refine ⟨67342415657711632793058203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44894943771807755195372135 67342415657711632793058203)
          ·
            refine ⟨101013623486567449189587305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67342415657711632793058203 101013623486567449189587305)
            ·
              refine ⟨75760217614925586892190479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101013623486567449189587305 75760217614925586892190479)
              ·
                refine ⟨113640326422388380338285719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75760217614925586892190479 113640326422388380338285719)
                ·
                  refine ⟨170460489633582570507428579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113640326422388380338285719 170460489633582570507428579)
                  ·
                    refine ⟨255690734450373855761142869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170460489633582570507428579 255690734450373855761142869)
                    ·
                      refine ⟨2996375794340318622200893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255690734450373855761142869 2996375794340318622200893)
                      ·
                        rfl

theorem cell23_5835421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5835421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835421 prefixEnd_5835421 := by exact prefixLift 5835421
  have htrace : WordTrace (prefixWord ++ tailWord_5835421) baseStart_5835421 baseEnd_5835421 := by
    simpa [prefixWord, tailWord_5835421, baseEnd_5835421] using wordTrace_append hprefix tailTrace_5835421
  have hstable : (prefixWord ++ tailWord_5835421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835421).length < 2 ^ (prefixWord ++ tailWord_5835421).sum := by decide
  have hdescent : baseEnd_5835421 < baseStart_5835421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835455 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 2, 3, 2]
def baseStart_5835455 : Nat := 118140960795 + 5835455 * 2 ^ 59
def prefixEnd_5835455 : Nat := 4983230072969 + 3 ^ 40 * 5835455 * 2
def baseEnd_5835455 : Nat := 2996393252682571489175737

theorem tailTrace_5835455 : CollatzResearch.WordTrace tailWord_5835455 prefixEnd_5835455 2996393252682571489175737 := by
  unfold tailWord_5835455
  simp only [CollatzResearch.WordTrace]
  refine ⟨212836529074150626214427819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141891019382767084142951879 212836529074150626214427819)
  ·
    refine ⟨319254793611225939321641729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212836529074150626214427819 319254793611225939321641729)
    ·
      refine ⟨239441095208419454491231297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319254793611225939321641729 239441095208419454491231297)
      ·
        refine ⟨179580821406314590868423473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239441095208419454491231297 179580821406314590868423473)
        ·
          refine ⟨134685616054735943151317605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179580821406314590868423473 134685616054735943151317605)
          ·
            refine ⟨25253553010262989340872051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134685616054735943151317605 25253553010262989340872051)
            ·
              refine ⟨37880329515394484011308077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25253553010262989340872051 37880329515394484011308077)
              ·
                refine ⟨14205123568272931504240529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37880329515394484011308077 14205123568272931504240529)
                ·
                  refine ⟨10653842676204698628180397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14205123568272931504240529 10653842676204698628180397)
                  ·
                    refine ⟨3995191003576761985567649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10653842676204698628180397 3995191003576761985567649)
                    ·
                      refine ⟨2996393252682571489175737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995191003576761985567649 2996393252682571489175737)
                      ·
                        rfl

theorem cell23_5835455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_5835455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835455 prefixEnd_5835455 := by exact prefixLift 5835455
  have htrace : WordTrace (prefixWord ++ tailWord_5835455) baseStart_5835455 baseEnd_5835455 := by
    simpa [prefixWord, tailWord_5835455, baseEnd_5835455] using wordTrace_append hprefix tailTrace_5835455
  have hstable : (prefixWord ++ tailWord_5835455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835455).length < 2 ^ (prefixWord ++ tailWord_5835455).sum := by decide
  have hdescent : baseEnd_5835455 < baseStart_5835455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835479 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 1, 1, 3]
def baseStart_5835479 : Nat := 118140960795 + 5835479 * 2 ^ 59
def prefixEnd_5835479 : Nat := 4983230072969 + 3 ^ 40 * 5835479 * 2
def baseEnd_5835479 : Nat := 2996405576218279395275627

theorem tailTrace_5835479 : CollatzResearch.WordTrace tailWord_5835479 prefixEnd_5835479 2996405576218279395275627 := by
  unfold tailWord_5835479
  simp only [CollatzResearch.WordTrace]
  refine ⟨212837404426063678313301491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141891602950709118875534327 212837404426063678313301491)
  ·
    refine ⟨319256106639095517469952237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212837404426063678313301491 319256106639095517469952237)
    ·
      refine ⟨119721039989660819051232089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319256106639095517469952237 119721039989660819051232089)
      ·
        refine ⟨89790779992245614288424067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119721039989660819051232089 89790779992245614288424067)
        ·
          refine ⟨134686169988368421432636101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89790779992245614288424067 134686169988368421432636101)
          ·
            refine ⟨25253656872819079018619269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134686169988368421432636101 25253656872819079018619269)
            ·
              refine ⟨4735060663653577315991113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25253656872819079018619269 4735060663653577315991113)
              ·
                refine ⟨3551295497740182986993335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735060663653577315991113 3551295497740182986993335)
                ·
                  refine ⟨5326943246610274480490003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551295497740182986993335 5326943246610274480490003)
                  ·
                    refine ⟨7990414869915411720735005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326943246610274480490003 7990414869915411720735005)
                    ·
                      refine ⟨2996405576218279395275627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990414869915411720735005 2996405576218279395275627)
                      ·
                        rfl

theorem cell23_5835479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_5835479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835479 prefixEnd_5835479 := by exact prefixLift 5835479
  have htrace : WordTrace (prefixWord ++ tailWord_5835479) baseStart_5835479 baseEnd_5835479 := by
    simpa [prefixWord, tailWord_5835479, baseEnd_5835479] using wordTrace_append hprefix tailTrace_5835479
  have hstable : (prefixWord ++ tailWord_5835479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835479).length < 2 ^ (prefixWord ++ tailWord_5835479).sum := by decide
  have hdescent : baseEnd_5835479 < baseStart_5835479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835502 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_5835502 : Nat := 118140960795 + 5835502 * 2 ^ 59
def prefixEnd_5835502 : Nat := 4983230072969 + 3 ^ 40 * 5835502 * 2
def baseEnd_5835502 : Nat := 2996417386273332805288021

theorem tailTrace_5835502 : CollatzResearch.WordTrace tailWord_5835502 prefixEnd_5835502 2996417386273332805288021 := by
  unfold tailWord_5835502
  simp only [CollatzResearch.WordTrace]
  refine ⟨26604780413122544155173595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141892162203320235494259173 26604780413122544155173595)
  ·
    refine ⟨39907170619683816232760393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26604780413122544155173595 39907170619683816232760393)
    ·
      refine ⟨29930377964762862174570295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39907170619683816232760393 29930377964762862174570295)
      ·
        refine ⟨44895566947144293261855443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29930377964762862174570295 44895566947144293261855443)
        ·
          refine ⟨67343350420716439892783165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44895566947144293261855443 67343350420716439892783165)
          ·
            refine ⟨25253756407768664959793687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67343350420716439892783165 25253756407768664959793687)
            ·
              refine ⟨37880634611652997439690531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25253756407768664959793687 37880634611652997439690531)
              ·
                refine ⟨56820951917479496159535797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37880634611652997439690531 56820951917479496159535797)
                ·
                  refine ⟨5326964242263702764956481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56820951917479496159535797 5326964242263702764956481)
                  ·
                    refine ⟨3995223181697777073717361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326964242263702764956481 3995223181697777073717361)
                    ·
                      refine ⟨2996417386273332805288021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995223181697777073717361 2996417386273332805288021)
                      ·
                        rfl

theorem cell23_5835502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_5835502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835502 prefixEnd_5835502 := by exact prefixLift 5835502
  have htrace : WordTrace (prefixWord ++ tailWord_5835502) baseStart_5835502 baseEnd_5835502 := by
    simpa [prefixWord, tailWord_5835502, baseEnd_5835502] using wordTrace_append hprefix tailTrace_5835502
  have hstable : (prefixWord ++ tailWord_5835502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835502).length < 2 ^ (prefixWord ++ tailWord_5835502).sum := by decide
  have hdescent : baseEnd_5835502 < baseStart_5835502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835505 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_5835505 : Nat := 118140960795 + 5835505 * 2 ^ 59
def prefixEnd_5835505 : Nat := 4983230072969 + 3 ^ 40 * 5835505 * 2
def baseEnd_5835505 : Nat := 2996418926715296293550507

theorem tailTrace_5835505 : CollatzResearch.WordTrace tailWord_5835505 prefixEnd_5835505 2996418926715296293550507 := by
  unfold tailWord_5835505
  simp only [CollatzResearch.WordTrace]
  refine ⟨212838352723969484753747969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141892235149312989835831979 212838352723969484753747969)
  ·
    refine ⟨159628764542977113565310977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212838352723969484753747969 159628764542977113565310977)
    ·
      refine ⟨119721573407232835173983233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159628764542977113565310977 119721573407232835173983233)
      ·
        refine ⟨89791180055424626380487425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119721573407232835173983233 89791180055424626380487425)
        ·
          refine ⟨67343385041568469785365569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89791180055424626380487425 67343385041568469785365569)
          ·
            refine ⟨50507538781176352339024177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67343385041568469785365569 50507538781176352339024177)
            ·
              refine ⟨37880654085882264254268133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50507538781176352339024177 37880654085882264254268133)
              ·
                refine ⟨7102622641102924547675275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37880654085882264254268133 7102622641102924547675275)
                ·
                  refine ⟨10653933961654386821512913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7102622641102924547675275 10653933961654386821512913)
                  ·
                    refine ⟨7990450471240790116134685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10653933961654386821512913 7990450471240790116134685)
                    ·
                      refine ⟨2996418926715296293550507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990450471240790116134685 2996418926715296293550507)
                      ·
                        rfl

theorem cell23_5835505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_5835505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835505 prefixEnd_5835505 := by exact prefixLift 5835505
  have htrace : WordTrace (prefixWord ++ tailWord_5835505) baseStart_5835505 baseEnd_5835505 := by
    simpa [prefixWord, tailWord_5835505, baseEnd_5835505] using wordTrace_append hprefix tailTrace_5835505
  have hstable : (prefixWord ++ tailWord_5835505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835505).length < 2 ^ (prefixWord ++ tailWord_5835505).sum := by decide
  have hdescent : baseEnd_5835505 < baseStart_5835505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835535 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 3]
def baseStart_5835535 : Nat := 118140960795 + 5835535 * 2 ^ 59
def prefixEnd_5835535 : Nat := 4983230072969 + 3 ^ 40 * 5835535 * 2
def baseEnd_5835535 : Nat := 2996434331134931176175369

theorem tailTrace_5835535 : CollatzResearch.WordTrace tailWord_5835535 prefixEnd_5835535 2996434331134931176175369 := by
  unfold tailWord_5835535
  simp only [CollatzResearch.WordTrace]
  refine ⟨212839446913860799877340059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141892964609240533251560039 212839446913860799877340059)
  ·
    refine ⟨319259170370791199816010089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212839446913860799877340059 319259170370791199816010089)
    ·
      refine ⟨239444377778093399862007567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319259170370791199816010089 239444377778093399862007567)
      ·
        refine ⟨359166566667140099793011351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239444377778093399862007567 359166566667140099793011351)
        ·
          refine ⟨538749850000710149689517027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359166566667140099793011351 538749850000710149689517027)
          ·
            refine ⟨808124775001065224534275541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538749850000710149689517027 808124775001065224534275541)
            ·
              refine ⟨18940424414087466200022083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 808124775001065224534275541 18940424414087466200022083)
              ·
                refine ⟨28410636621131199300033125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18940424414087466200022083 28410636621131199300033125)
                ·
                  refine ⟨5326994366462099868756211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28410636621131199300033125 5326994366462099868756211)
                  ·
                    refine ⟨7990491549693149803134317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326994366462099868756211 7990491549693149803134317)
                    ·
                      refine ⟨2996434331134931176175369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990491549693149803134317 2996434331134931176175369)
                      ·
                        rfl

theorem cell23_5835535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_5835535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835535 prefixEnd_5835535 := by exact prefixLift 5835535
  have htrace : WordTrace (prefixWord ++ tailWord_5835535) baseStart_5835535 baseEnd_5835535 := by
    simpa [prefixWord, tailWord_5835535, baseEnd_5835535] using wordTrace_append hprefix tailTrace_5835535
  have hstable : (prefixWord ++ tailWord_5835535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835535).length < 2 ^ (prefixWord ++ tailWord_5835535).sum := by decide
  have hdescent : baseEnd_5835535 < baseStart_5835535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835545 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 3, 3, 2]
def baseStart_5835545 : Nat := 118140960795 + 5835545 * 2 ^ 59
def prefixEnd_5835545 : Nat := 4983230072969 + 3 ^ 40 * 5835545 * 2
def baseEnd_5835545 : Nat := 2996439465941476137050323

theorem tailTrace_5835545 : CollatzResearch.WordTrace tailWord_5835545 prefixEnd_5835545 2996439465941476137050323 := by
  unfold tailWord_5835545
  simp only [CollatzResearch.WordTrace]
  refine ⟨212839811643824571585204089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141893207762549714390136059 212839811643824571585204089)
  ·
    refine ⟨159629858732868428688903067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212839811643824571585204089 159629858732868428688903067)
    ·
      refine ⟨239444788099302643033354601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159629858732868428688903067 239444788099302643033354601)
      ·
        refine ⟨179583591074476982275015951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239444788099302643033354601 179583591074476982275015951)
        ·
          refine ⟨269375386611715473412523927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179583591074476982275015951 269375386611715473412523927)
          ·
            refine ⟨404063079917573210118785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269375386611715473412523927 404063079917573210118785891)
            ·
              refine ⟨606094619876359815178178837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404063079917573210118785891 606094619876359815178178837)
              ·
                refine ⟨28410685306704366336477133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 606094619876359815178178837 28410685306704366336477133)
                ·
                  refine ⟨10654006990014137376178925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28410685306704366336477133 10654006990014137376178925)
                  ·
                    refine ⟨3995252621255301516067097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10654006990014137376178925 3995252621255301516067097)
                    ·
                      refine ⟨2996439465941476137050323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995252621255301516067097 2996439465941476137050323)
                      ·
                        rfl

theorem cell23_5835545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_5835545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835545 prefixEnd_5835545 := by exact prefixLift 5835545
  have htrace : WordTrace (prefixWord ++ tailWord_5835545) baseStart_5835545 baseEnd_5835545 := by
    simpa [prefixWord, tailWord_5835545, baseEnd_5835545] using wordTrace_append hprefix tailTrace_5835545
  have hstable : (prefixWord ++ tailWord_5835545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835545).length < 2 ^ (prefixWord ++ tailWord_5835545).sum := by decide
  have hdescent : baseEnd_5835545 < baseStart_5835545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835549 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5835549 : Nat := 118140960795 + 5835549 * 2 ^ 59
def prefixEnd_5835549 : Nat := 4983230072969 + 3 ^ 40 * 5835549 * 2
def baseEnd_5835549 : Nat := 2996441519864094121400305

theorem tailTrace_5835549 : CollatzResearch.WordTrace tailWord_5835549 prefixEnd_5835549 2996441519864094121400305 := by
  unfold tailWord_5835549
  simp only [CollatzResearch.WordTrace]
  refine ⟨212839957535810080268349701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141893305023873386845566467 212839957535810080268349701)
  ·
    refine ⟨39907492037964390050315569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212839957535810080268349701 39907492037964390050315569)
    ·
      refine ⟨29930619028473292537736677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39907492037964390050315569 29930619028473292537736677)
      ·
        refine ⟨5611991067838742350825627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29930619028473292537736677 5611991067838742350825627)
        ·
          refine ⟨8417986601758113526238441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611991067838742350825627 8417986601758113526238441)
          ·
            refine ⟨6313489951318585144678831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8417986601758113526238441 6313489951318585144678831)
            ·
              refine ⟨9470234926977877717018247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313489951318585144678831 9470234926977877717018247)
              ·
                refine ⟨14205352390466816575527371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470234926977877717018247 14205352390466816575527371)
                ·
                  refine ⟨21308028585700224863291057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14205352390466816575527371 21308028585700224863291057)
                  ·
                    refine ⟨15981021439275168647468293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21308028585700224863291057 15981021439275168647468293)
                    ·
                      refine ⟨2996441519864094121400305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15981021439275168647468293 2996441519864094121400305)
                      ·
                        rfl

theorem cell23_5835549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5835549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835549 prefixEnd_5835549 := by exact prefixLift 5835549
  have htrace : WordTrace (prefixWord ++ tailWord_5835549) baseStart_5835549 baseEnd_5835549 := by
    simpa [prefixWord, tailWord_5835549, baseEnd_5835549] using wordTrace_append hprefix tailTrace_5835549
  have hstable : (prefixWord ++ tailWord_5835549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835549).length < 2 ^ (prefixWord ++ tailWord_5835549).sum := by decide
  have hdescent : baseEnd_5835549 < baseStart_5835549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835552 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5835552 : Nat := 118140960795 + 5835552 * 2 ^ 59
def prefixEnd_5835552 : Nat := 4983230072969 + 3 ^ 40 * 5835552 * 2
def baseEnd_5835552 : Nat := 2996443060306057609662791

theorem tailTrace_5835552 : CollatzResearch.WordTrace tailWord_5835552 prefixEnd_5835552 2996443060306057609662791 := by
  unfold tailWord_5835552
  simp only [CollatzResearch.WordTrace]
  refine ⟨106420033477399605890354455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141893377969866141187139273 106420033477399605890354455)
  ·
    refine ⟨159630050216099408835531683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106420033477399605890354455 159630050216099408835531683)
    ·
      refine ⟨239445075324149113253297525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159630050216099408835531683 239445075324149113253297525)
      ·
        refine ⟨22447975811638979367496643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239445075324149113253297525 22447975811638979367496643)
        ·
          refine ⟨33671963717458469051244965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22447975811638979367496643 33671963717458469051244965)
          ·
            refine ⟨6313493197023462947108431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33671963717458469051244965 6313493197023462947108431)
            ·
              refine ⟨9470239795535194420662647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313493197023462947108431 9470239795535194420662647)
              ·
                refine ⟨14205359693302791630993971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470239795535194420662647 14205359693302791630993971)
                ·
                  refine ⟨21308039539954187446490957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14205359693302791630993971 21308039539954187446490957)
                  ·
                    refine ⟨7990514827482820292434109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21308039539954187446490957 7990514827482820292434109)
                    ·
                      refine ⟨2996443060306057609662791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990514827482820292434109 2996443060306057609662791)
                      ·
                        rfl

theorem cell23_5835552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5835552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835552 prefixEnd_5835552 := by exact prefixLift 5835552
  have htrace : WordTrace (prefixWord ++ tailWord_5835552) baseStart_5835552 baseEnd_5835552 := by
    simpa [prefixWord, tailWord_5835552, baseEnd_5835552] using wordTrace_append hprefix tailTrace_5835552
  have hstable : (prefixWord ++ tailWord_5835552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835552).length < 2 ^ (prefixWord ++ tailWord_5835552).sum := by decide
  have hdescent : baseEnd_5835552 < baseStart_5835552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835575 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_5835575 : Nat := 118140960795 + 5835575 * 2 ^ 59
def prefixEnd_5835575 : Nat := 4983230072969 + 3 ^ 40 * 5835575 * 2
def baseEnd_5835575 : Nat := 2996454870361111019675185

theorem tailTrace_5835575 : CollatzResearch.WordTrace tailWord_5835575 prefixEnd_5835575 2996454870361111019675185 := by
  unfold tailWord_5835575
  simp only [CollatzResearch.WordTrace]
  refine ⟨212840905833715886708796179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141893937222477257805864119 212840905833715886708796179)
  ·
    refine ⟨319261358750573830063194269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212840905833715886708796179 319261358750573830063194269)
    ·
      refine ⟨119723009531465186273697851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319261358750573830063194269 119723009531465186273697851)
      ·
        refine ⟨179584514297197779410546777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119723009531465186273697851 179584514297197779410546777)
        ·
          refine ⟨134688385722898334557910083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179584514297197779410546777 134688385722898334557910083)
          ·
            refine ⟨202032578584347501836865125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134688385722898334557910083 202032578584347501836865125)
            ·
              refine ⟨37881108484565156594412211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202032578584347501836865125 37881108484565156594412211)
              ·
                refine ⟨56821662726847734891618317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37881108484565156594412211 56821662726847734891618317)
                ·
                  refine ⟨21308123522567900584356869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56821662726847734891618317 21308123522567900584356869)
                  ·
                    refine ⟨3995273160481481359566913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21308123522567900584356869 3995273160481481359566913)
                    ·
                      refine ⟨2996454870361111019675185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995273160481481359566913 2996454870361111019675185)
                      ·
                        rfl

theorem cell23_5835575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_5835575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835575 prefixEnd_5835575 := by exact prefixLift 5835575
  have htrace : WordTrace (prefixWord ++ tailWord_5835575) baseStart_5835575 baseEnd_5835575 := by
    simpa [prefixWord, tailWord_5835575, baseEnd_5835575] using wordTrace_append hprefix tailTrace_5835575
  have hstable : (prefixWord ++ tailWord_5835575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835575).length < 2 ^ (prefixWord ++ tailWord_5835575).sum := by decide
  have hdescent : baseEnd_5835575 < baseStart_5835575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835592 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_5835592 : Nat := 118140960795 + 5835592 * 2 ^ 59
def prefixEnd_5835592 : Nat := 4983230072969 + 3 ^ 40 * 5835592 * 2
def baseEnd_5835592 : Nat := 2996463599532237453162607

theorem tailTrace_5835592 : CollatzResearch.WordTrace tailWord_5835592 prefixEnd_5835592 2996463599532237453162607 := by
  unfold tailWord_5835592
  simp only [CollatzResearch.WordTrace]
  refine ⟨106420762937327149306082515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141894350583102865741443353 106420762937327149306082515)
  ·
    refine ⟨159631144405990723959123773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106420762937327149306082515 159631144405990723959123773)
    ·
      refine ⟨59861679152246521484671415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159631144405990723959123773 59861679152246521484671415)
      ·
        refine ⟨89792518728369782227007123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59861679152246521484671415 89792518728369782227007123)
        ·
          refine ⟨134688778092554673340510685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89792518728369782227007123 134688778092554673340510685)
          ·
            refine ⟨50508291784708002502691507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134688778092554673340510685 50508291784708002502691507)
            ·
              refine ⟨75762437677062003754037261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50508291784708002502691507 75762437677062003754037261)
              ·
                refine ⟨28410914128898251407763973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75762437677062003754037261 28410914128898251407763973)
                ·
                  refine ⟨5327046399168422138955745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28410914128898251407763973 5327046399168422138955745)
                  ·
                    refine ⟨3995284799376316604216809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5327046399168422138955745 3995284799376316604216809)
                    ·
                      refine ⟨2996463599532237453162607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995284799376316604216809 2996463599532237453162607)
                      ·
                        rfl

theorem cell23_5835592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_5835592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835592 prefixEnd_5835592 := by exact prefixLift 5835592
  have htrace : WordTrace (prefixWord ++ tailWord_5835592) baseStart_5835592 baseEnd_5835592 := by
    simpa [prefixWord, tailWord_5835592, baseEnd_5835592] using wordTrace_append hprefix tailTrace_5835592
  have hstable : (prefixWord ++ tailWord_5835592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835592).length < 2 ^ (prefixWord ++ tailWord_5835592).sum := by decide
  have hdescent : baseEnd_5835592 < baseStart_5835592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835609 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 2, 2, 2]
def baseStart_5835609 : Nat := 118140960795 + 5835609 * 2 ^ 59
def prefixEnd_5835609 : Nat := 4983230072969 + 3 ^ 40 * 5835609 * 2
def baseEnd_5835609 : Nat := 2996472328703363886650029

theorem tailTrace_5835609 : CollatzResearch.WordTrace tailWord_5835609 prefixEnd_5835609 2996472328703363886650029 := by
  unfold tailWord_5835609
  simp only [CollatzResearch.WordTrace]
  refine ⟨212842145915592710515533881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141894763943728473677022587 212842145915592710515533881)
  ·
    refine ⟨159631609436694532886650411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212842145915592710515533881 159631609436694532886650411)
    ·
      refine ⟨239447414155041799329975617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159631609436694532886650411 239447414155041799329975617)
      ·
        refine ⟨179585560616281349497481713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239447414155041799329975617 179585560616281349497481713)
        ·
          refine ⟨134689170462211012123111285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179585560616281349497481713 134689170462211012123111285)
          ·
            refine ⟨12627109730832282386541683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134689170462211012123111285 12627109730832282386541683)
            ·
              refine ⟨18940664596248423579812525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627109730832282386541683 18940664596248423579812525)
              ·
                refine ⟨7102749223593158842429697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18940664596248423579812525 7102749223593158842429697)
                ·
                  refine ⟨5327061917694869131822273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102749223593158842429697 5327061917694869131822273)
                  ·
                    refine ⟨3995296438271151848866705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5327061917694869131822273 3995296438271151848866705)
                    ·
                      refine ⟨2996472328703363886650029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995296438271151848866705 2996472328703363886650029)
                      ·
                        rfl

theorem cell23_5835609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_5835609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835609 prefixEnd_5835609 := by exact prefixLift 5835609
  have htrace : WordTrace (prefixWord ++ tailWord_5835609) baseStart_5835609 baseEnd_5835609 := by
    simpa [prefixWord, tailWord_5835609, baseEnd_5835609] using wordTrace_append hprefix tailTrace_5835609
  have hstable : (prefixWord ++ tailWord_5835609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835609).length < 2 ^ (prefixWord ++ tailWord_5835609).sum := by decide
  have hdescent : baseEnd_5835609 < baseStart_5835609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835645 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_5835645 : Nat := 118140960795 + 5835645 * 2 ^ 59
def prefixEnd_5835645 : Nat := 4983230072969 + 3 ^ 40 * 5835645 * 2
def baseEnd_5835645 : Nat := 998830271335641915266621

theorem tailTrace_5835645 : CollatzResearch.WordTrace tailWord_5835645 prefixEnd_5835645 998830271335641915266621 := by
  unfold tailWord_5835645
  simp only [CollatzResearch.WordTrace]
  refine ⟨212843458943462288663844389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141895639295641525775896259 212843458943462288663844389)
  ·
    refine ⟨39908148551899179124470823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212843458943462288663844389 39908148551899179124470823)
    ·
      refine ⟨59862222827848768686706235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39908148551899179124470823 59862222827848768686706235)
      ·
        refine ⟨89793334241773153030059353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59862222827848768686706235 89793334241773153030059353)
        ·
          refine ⟨67345000681329864772544515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89793334241773153030059353 67345000681329864772544515)
          ·
            refine ⟨101017501021994797158816773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67345000681329864772544515 101017501021994797158816773)
            ·
              refine ⟨18940781441624024467278145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101017501021994797158816773 18940781441624024467278145)
              ·
                refine ⟨14205586081218018350458609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18940781441624024467278145 14205586081218018350458609)
                ·
                  refine ⟨10654189560913513762843957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14205586081218018350458609 10654189560913513762843957)
                  ·
                    refine ⟨998830271335641915266621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10654189560913513762843957 998830271335641915266621)
                    ·
                      rfl

theorem cell23_5835645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_5835645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835645 prefixEnd_5835645 := by exact prefixLift 5835645
  have htrace : WordTrace (prefixWord ++ tailWord_5835645) baseStart_5835645 baseEnd_5835645 := by
    simpa [prefixWord, tailWord_5835645, baseEnd_5835645] using wordTrace_append hprefix tailTrace_5835645
  have hstable : (prefixWord ++ tailWord_5835645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835645).length < 2 ^ (prefixWord ++ tailWord_5835645).sum := by decide
  have hdescent : baseEnd_5835645 < baseStart_5835645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835655 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_5835655 : Nat := 118140960795 + 5835655 * 2 ^ 59
def prefixEnd_5835655 : Nat := 4983230072969 + 3 ^ 40 * 5835655 * 2
def baseEnd_5835655 : Nat := 2996495948813470706674817

theorem tailTrace_5835655 : CollatzResearch.WordTrace tailWord_5835655 prefixEnd_5835655 2996495948813470706674817 := by
  unfold tailWord_5835655
  simp only [CollatzResearch.WordTrace]
  refine ⟨212843823673426060371708419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141895882448950706914472279 212843823673426060371708419)
  ·
    refine ⟨319265735510139090557562629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212843823673426060371708419 319265735510139090557562629)
    ·
      refine ⟨59862325408151079479542993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319265735510139090557562629 59862325408151079479542993)
      ·
        refine ⟨44896744056113309609657245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59862325408151079479542993 44896744056113309609657245)
        ·
          refine ⟨16836279021042491103621467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44896744056113309609657245 16836279021042491103621467)
          ·
            refine ⟨25254418531563736655432201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16836279021042491103621467 25254418531563736655432201)
            ·
              refine ⟨18940813898672802491574151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25254418531563736655432201 18940813898672802491574151)
              ·
                refine ⟨28411220848009203737361227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18940813898672802491574151 28411220848009203737361227)
                ·
                  refine ⟨42616831272013805606041841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28411220848009203737361227 42616831272013805606041841)
                  ·
                    refine ⟨31962623454010354204531381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42616831272013805606041841 31962623454010354204531381)
                    ·
                      refine ⟨2996495948813470706674817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31962623454010354204531381 2996495948813470706674817)
                      ·
                        rfl

theorem cell23_5835655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_5835655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835655 prefixEnd_5835655 := by exact prefixLift 5835655
  have htrace : WordTrace (prefixWord ++ tailWord_5835655) baseStart_5835655 baseEnd_5835655 := by
    simpa [prefixWord, tailWord_5835655, baseEnd_5835655] using wordTrace_append hprefix tailTrace_5835655
  have hstable : (prefixWord ++ tailWord_5835655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835655).length < 2 ^ (prefixWord ++ tailWord_5835655).sum := by decide
  have hdescent : baseEnd_5835655 < baseStart_5835655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835682 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5835682 : Nat := 118140960795 + 5835682 * 2 ^ 59
def prefixEnd_5835682 : Nat := 4983230072969 + 3 ^ 40 * 5835682 * 2
def baseEnd_5835682 : Nat := 2996509812791142101037193

theorem tailTrace_5835682 : CollatzResearch.WordTrace tailWord_5835682 prefixEnd_5835682 2996509812791142101037193 := by
  unfold tailWord_5835682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53211202111082060995735325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141896538962885495988627533 53211202111082060995735325)
  ·
    refine ⟨19954200791655772873400747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53211202111082060995735325 19954200791655772873400747)
    ·
      refine ⟨29931301187483659310101121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19954200791655772873400747 29931301187483659310101121)
      ·
        refine ⟨22448475890612744482575841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29931301187483659310101121 22448475890612744482575841)
        ·
          refine ⟨16836356917959558361931881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22448475890612744482575841 16836356917959558361931881)
          ·
            refine ⟨12627267688469668771448911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16836356917959558361931881 12627267688469668771448911)
            ·
              refine ⟨18940901532704503157173367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627267688469668771448911 18940901532704503157173367)
              ·
                refine ⟨28411352299056754735760051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18940901532704503157173367 28411352299056754735760051)
                ·
                  refine ⟨42617028448585132103640077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28411352299056754735760051 42617028448585132103640077)
                  ·
                    refine ⟨15981385668219424538865029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42617028448585132103640077 15981385668219424538865029)
                    ·
                      refine ⟨2996509812791142101037193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15981385668219424538865029 2996509812791142101037193)
                      ·
                        rfl

theorem cell23_5835682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5835682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835682 prefixEnd_5835682 := by exact prefixLift 5835682
  have htrace : WordTrace (prefixWord ++ tailWord_5835682) baseStart_5835682 baseEnd_5835682 := by
    simpa [prefixWord, tailWord_5835682, baseEnd_5835682] using wordTrace_append hprefix tailTrace_5835682
  have hstable : (prefixWord ++ tailWord_5835682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835682).length < 2 ^ (prefixWord ++ tailWord_5835682).sum := by decide
  have hdescent : baseEnd_5835682 < baseStart_5835682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835705 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 8]
def baseStart_5835705 : Nat := 118140960795 + 5835705 * 2 ^ 59
def prefixEnd_5835705 : Nat := 4983230072969 + 3 ^ 40 * 5835705 * 2
def baseEnd_5835705 : Nat := 332946846982910612338843

theorem tailTrace_5835705 : CollatzResearch.WordTrace tailWord_5835705 prefixEnd_5835705 332946846982910612338843 := by
  unfold tailWord_5835705
  simp only [CollatzResearch.WordTrace]
  refine ⟨212845647323244918911028569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141897098215496612607352379 212845647323244918911028569)
  ·
    refine ⟨159634235492433689183271427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212845647323244918911028569 159634235492433689183271427)
    ·
      refine ⟨239451353238650533774907141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159634235492433689183271427 239451353238650533774907141)
      ·
        refine ⟨44897128732246975082795089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239451353238650533774907141 44897128732246975082795089)
        ·
          refine ⟨33672846549185231312096317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44897128732246975082795089 33672846549185231312096317)
          ·
            refine ⟨12627317455944461742036119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33672846549185231312096317 12627317455944461742036119)
            ·
              refine ⟨18940976183916692613054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627317455944461742036119 18940976183916692613054179)
              ·
                refine ⟨28411464275875038919581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18940976183916692613054179 28411464275875038919581269)
                ·
                  refine ⟨332946846982910612338843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28411464275875038919581269 332946846982910612338843)
                  ·
                    rfl

theorem cell23_5835705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_5835705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835705 prefixEnd_5835705 := by exact prefixLift 5835705
  have htrace : WordTrace (prefixWord ++ tailWord_5835705) baseStart_5835705 baseEnd_5835705 := by
    simpa [prefixWord, tailWord_5835705, baseEnd_5835705] using wordTrace_append hprefix tailTrace_5835705
  have hstable : (prefixWord ++ tailWord_5835705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835705).length < 2 ^ (prefixWord ++ tailWord_5835705).sum := by decide
  have hdescent : baseEnd_5835705 < baseStart_5835705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835709 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_5835709 : Nat := 118140960795 + 5835709 * 2 ^ 59
def prefixEnd_5835709 : Nat := 4983230072969 + 3 ^ 40 * 5835709 * 2
def baseEnd_5835709 : Nat := 998841225589604498466523

theorem tailTrace_5835709 : CollatzResearch.WordTrace tailWord_5835709 prefixEnd_5835709 998841225589604498466523 := by
  unfold tailWord_5835709
  simp only [CollatzResearch.WordTrace]
  refine ⟨212845793215230427594174181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141897195476820285062782787 212845793215230427594174181)
  ·
    refine ⟨39908586227855705173907659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212845793215230427594174181 39908586227855705173907659)
    ·
      refine ⟨59862879341783557760861489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39908586227855705173907659 59862879341783557760861489)
      ·
        refine ⟨44897159506337668320646117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59862879341783557760861489 44897159506337668320646117)
        ·
          refine ⟨8418217407438312810121147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44897159506337668320646117 8418217407438312810121147)
          ·
            refine ⟨12627326111157469215181721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418217407438312810121147 12627326111157469215181721)
            ·
              refine ⟨9470494583368101911386291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12627326111157469215181721 9470494583368101911386291)
              ·
                refine ⟨14205741875052152867079437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470494583368101911386291 14205741875052152867079437)
                ·
                  refine ⟨5327153203144557325154789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14205741875052152867079437 5327153203144557325154789)
                  ·
                    refine ⟨998841225589604498466523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327153203144557325154789 998841225589604498466523)
                    ·
                      rfl

theorem cell23_5835709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_5835709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835709 prefixEnd_5835709 := by exact prefixLift 5835709
  have htrace : WordTrace (prefixWord ++ tailWord_5835709) baseStart_5835709 baseEnd_5835709 := by
    simpa [prefixWord, tailWord_5835709, baseEnd_5835709] using wordTrace_append hprefix tailTrace_5835709
  have hstable : (prefixWord ++ tailWord_5835709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835709).length < 2 ^ (prefixWord ++ tailWord_5835709).sum := by decide
  have hdescent : baseEnd_5835709 < baseStart_5835709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835743 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 1, 4]
def baseStart_5835743 : Nat := 118140960795 + 5835743 * 2 ^ 59
def prefixEnd_5835743 : Nat := 4983230072969 + 3 ^ 40 * 5835743 * 2
def baseEnd_5835743 : Nat := 998847045037022120791471

theorem tailTrace_5835743 : CollatzResearch.WordTrace tailWord_5835743 prefixEnd_5835743 998847045037022120791471 := by
  unfold tailWord_5835743
  simp only [CollatzResearch.WordTrace]
  refine ⟨212847033297107251400911883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141898022198071500933941255 212847033297107251400911883)
  ·
    refine ⟨319270549945660877101367825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212847033297107251400911883 319270549945660877101367825)
    ·
      refine ⟨239452912459245657826025869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319270549945660877101367825 239452912459245657826025869)
      ·
        refine ⟨89794842172217121684759701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239452912459245657826025869 89794842172217121684759701)
        ·
          refine ⟨4209133226822677578973111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89794842172217121684759701 4209133226822677578973111)
          ·
            refine ⟨6313699840234016368459667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209133226822677578973111 6313699840234016368459667)
            ·
              refine ⟨9470549760351024552689501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313699840234016368459667 9470549760351024552689501)
              ·
                refine ⟨3551456160131634207258563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9470549760351024552689501 3551456160131634207258563)
                ·
                  refine ⟨5327184240197451310887845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551456160131634207258563 5327184240197451310887845)
                  ·
                    refine ⟨998847045037022120791471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327184240197451310887845 998847045037022120791471)
                    ·
                      rfl

theorem cell23_5835743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 4].length) (baseStart_5835743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835743 prefixEnd_5835743 := by exact prefixLift 5835743
  have htrace : WordTrace (prefixWord ++ tailWord_5835743) baseStart_5835743 baseEnd_5835743 := by
    simpa [prefixWord, tailWord_5835743, baseEnd_5835743] using wordTrace_append hprefix tailTrace_5835743
  have hstable : (prefixWord ++ tailWord_5835743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835743).length < 2 ^ (prefixWord ++ tailWord_5835743).sum := by decide
  have hdescent : baseEnd_5835743 < baseStart_5835743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835752 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5835752 : Nat := 118140960795 + 5835752 * 2 ^ 59
def prefixEnd_5835752 : Nat := 4983230072969 + 3 ^ 40 * 5835752 * 2
def baseEnd_5835752 : Nat := 998848585478985609053957

theorem tailTrace_5835752 : CollatzResearch.WordTrace tailWord_5835752 prefixEnd_5835752 998848585478985609053957 := by
  unfold tailWord_5835752
  simp only [CollatzResearch.WordTrace]
  refine ⟨106423680777037322968994755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141898241036049763958659673 106423680777037322968994755)
  ·
    refine ⟨159635521165555984453492133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106423680777037322968994755 159635521165555984453492133)
    ·
      refine ⟨29931660218541747085029775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159635521165555984453492133 29931660218541747085029775)
      ·
        refine ⟨44897490327812620627544663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29931660218541747085029775 44897490327812620627544663)
        ·
          refine ⟨67346235491718930941316995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44897490327812620627544663 67346235491718930941316995)
          ·
            refine ⟨101019353237578396411975493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67346235491718930941316995 101019353237578396411975493)
            ·
              refine ⟨18941128732045949327245405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101019353237578396411975493 18941128732045949327245405)
              ·
                refine ⟨7102923274517230997717027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18941128732045949327245405 7102923274517230997717027)
                ·
                  refine ⟨10654384911775846496575541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7102923274517230997717027 10654384911775846496575541)
                  ·
                    refine ⟨998848585478985609053957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10654384911775846496575541 998848585478985609053957)
                    ·
                      rfl

theorem cell23_5835752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5835752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835752 prefixEnd_5835752 := by exact prefixLift 5835752
  have htrace : WordTrace (prefixWord ++ tailWord_5835752) baseStart_5835752 baseEnd_5835752 := by
    simpa [prefixWord, tailWord_5835752, baseEnd_5835752] using wordTrace_append hprefix tailTrace_5835752
  have hstable : (prefixWord ++ tailWord_5835752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835752).length < 2 ^ (prefixWord ++ tailWord_5835752).sum := by decide
  have hdescent : baseEnd_5835752 < baseStart_5835752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835755 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4]
def baseStart_5835755 : Nat := 118140960795 + 5835755 * 2 ^ 59
def prefixEnd_5835755 : Nat := 4983230072969 + 3 ^ 40 * 5835755 * 2
def baseEnd_5835755 : Nat := 2996547296878920315424357

theorem tailTrace_5835755 : CollatzResearch.WordTrace tailWord_5835755 prefixEnd_5835755 2996547296878920315424357 := by
  unfold tailWord_5835755
  simp only [CollatzResearch.WordTrace]
  refine ⟨212847470973063777450348719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141898313982042518300232479 212847470973063777450348719)
  ·
    refine ⟨319271206459595666175523079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212847470973063777450348719 319271206459595666175523079)
    ·
      refine ⟨478906809689393499263284619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319271206459595666175523079 478906809689393499263284619)
      ·
        refine ⟨718360214534090248894926929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478906809689393499263284619 718360214534090248894926929)
        ·
          refine ⟨538770160900567686671195197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718360214534090248894926929 538770160900567686671195197)
          ·
            refine ⟨202038810337712882501698199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538770160900567686671195197 202038810337712882501698199)
            ·
              refine ⟨303058215506569323752547299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202038810337712882501698199 303058215506569323752547299)
              ·
                refine ⟨454587323259853985628820949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303058215506569323752547299 454587323259853985628820949)
                ·
                  refine ⟨10654390388902827788175491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 454587323259853985628820949 10654390388902827788175491)
                  ·
                    refine ⟨15981585583354241682263237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10654390388902827788175491 15981585583354241682263237)
                    ·
                      refine ⟨2996547296878920315424357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15981585583354241682263237 2996547296878920315424357)
                      ·
                        rfl

theorem cell23_5835755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4].length) (baseStart_5835755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835755 prefixEnd_5835755 := by exact prefixLift 5835755
  have htrace : WordTrace (prefixWord ++ tailWord_5835755) baseStart_5835755 baseEnd_5835755 := by
    simpa [prefixWord, tailWord_5835755, baseEnd_5835755] using wordTrace_append hprefix tailTrace_5835755
  have hstable : (prefixWord ++ tailWord_5835755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835755).length < 2 ^ (prefixWord ++ tailWord_5835755).sum := by decide
  have hdescent : baseEnd_5835755 < baseStart_5835755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835759 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 2, 3, 2]
def baseStart_5835759 : Nat := 118140960795 + 5835759 * 2 ^ 59
def prefixEnd_5835759 : Nat := 4983230072969 + 3 ^ 40 * 5835759 * 2
def baseEnd_5835759 : Nat := 2996549350801538299774339

theorem tailTrace_5835759 : CollatzResearch.WordTrace tailWord_5835759 prefixEnd_5835759 2996549350801538299774339 := by
  unfold tailWord_5835759
  simp only [CollatzResearch.WordTrace]
  refine ⟨212847616865049286133494331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141898411243366190755662887 212847616865049286133494331)
  ·
    refine ⟨319271425297573929200241497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212847616865049286133494331 319271425297573929200241497)
    ·
      refine ⟨239453568973180446900181123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319271425297573929200241497 239453568973180446900181123)
      ·
        refine ⟨359180353459770670350271685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239453568973180446900181123 359180353459770670350271685)
        ·
          refine ⟨67346316273707000690675941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359180353459770670350271685 67346316273707000690675941)
          ·
            refine ⟨12627434301320062629501739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67346316273707000690675941 12627434301320062629501739)
            ·
              refine ⟨18941151451980093944252609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627434301320062629501739 18941151451980093944252609)
              ·
                refine ⟨14205863588985070458189457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18941151451980093944252609 14205863588985070458189457)
                ·
                  refine ⟨10654397691738802843642093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14205863588985070458189457 10654397691738802843642093)
                  ·
                    refine ⟨3995399134402051066365785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10654397691738802843642093 3995399134402051066365785)
                    ·
                      refine ⟨2996549350801538299774339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995399134402051066365785 2996549350801538299774339)
                      ·
                        rfl

theorem cell23_5835759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3, 2].length) (baseStart_5835759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835759 prefixEnd_5835759 := by exact prefixLift 5835759
  have htrace : WordTrace (prefixWord ++ tailWord_5835759) baseStart_5835759 baseEnd_5835759 := by
    simpa [prefixWord, tailWord_5835759, baseEnd_5835759] using wordTrace_append hprefix tailTrace_5835759
  have hstable : (prefixWord ++ tailWord_5835759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835759).length < 2 ^ (prefixWord ++ tailWord_5835759).sum := by decide
  have hdescent : baseEnd_5835759 < baseStart_5835759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835766 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5835766 : Nat := 118140960795 + 5835766 * 2 ^ 59
def prefixEnd_5835766 : Nat := 4983230072969 + 3 ^ 40 * 5835766 * 2
def baseEnd_5835766 : Nat := 2996552945166119772386807

theorem tailTrace_5835766 : CollatzResearch.WordTrace tailWord_5835766 prefixEnd_5835766 2996552945166119772386807 := by
  unfold tailWord_5835766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302992011001495395562447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141898581450682617552666101 13302992011001495395562447)
  ·
    refine ⟨19954488016502243093343671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13302992011001495395562447 19954488016502243093343671)
    ·
      refine ⟨29931732024753364640015507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19954488016502243093343671 29931732024753364640015507)
      ·
        refine ⟨44897598037130046960023261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29931732024753364640015507 44897598037130046960023261)
        ·
          refine ⟨16836599263923767610008723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44897598037130046960023261 16836599263923767610008723)
          ·
            refine ⟨25254898895885651415013085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16836599263923767610008723 25254898895885651415013085)
            ·
              refine ⟨9470587085957119280629907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25254898895885651415013085 9470587085957119280629907)
              ·
                refine ⟨14205880628935678920944861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470587085957119280629907 14205880628935678920944861)
                ·
                  refine ⟨5327205235850879595354323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14205880628935678920944861 5327205235850879595354323)
                  ·
                    refine ⟨7990807853776319393031485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5327205235850879595354323 7990807853776319393031485)
                    ·
                      refine ⟨2996552945166119772386807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990807853776319393031485 2996552945166119772386807)
                      ·
                        rfl

theorem cell23_5835766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5835766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835766 prefixEnd_5835766 := by exact prefixLift 5835766
  have htrace : WordTrace (prefixWord ++ tailWord_5835766) baseStart_5835766 baseEnd_5835766 := by
    simpa [prefixWord, tailWord_5835766, baseEnd_5835766] using wordTrace_append hprefix tailTrace_5835766
  have hstable : (prefixWord ++ tailWord_5835766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835766).length < 2 ^ (prefixWord ++ tailWord_5835766).sum := by decide
  have hdescent : baseEnd_5835766 < baseStart_5835766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835775 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_5835775 : Nat := 118140960795 + 5835775 * 2 ^ 59
def prefixEnd_5835775 : Nat := 4983230072969 + 3 ^ 40 * 5835775 * 2
def baseEnd_5835775 : Nat := 2996557566492010237174265

theorem tailTrace_5835775 : CollatzResearch.WordTrace tailWord_5835775 prefixEnd_5835775 2996557566492010237174265 := by
  unfold tailWord_5835775
  simp only [CollatzResearch.WordTrace]
  refine ⟨212848200432991320866076779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141898800288660880577384519 212848200432991320866076779)
  ·
    refine ⟨319272300649486981299115169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212848200432991320866076779 319272300649486981299115169)
    ·
      refine ⟨239454225487115235974336377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319272300649486981299115169 239454225487115235974336377)
      ·
        refine ⟨179590669115336426980752283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239454225487115235974336377 179590669115336426980752283)
        ·
          refine ⟨269386003673004640471128425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179590669115336426980752283 269386003673004640471128425)
          ·
            refine ⟨202039502754753480353346319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269386003673004640471128425 202039502754753480353346319)
            ·
              refine ⟨303059254132130220530019479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202039502754753480353346319 303059254132130220530019479)
              ·
                refine ⟨454588881198195330795029219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303059254132130220530019479 454588881198195330795029219)
                ·
                  refine ⟨681883321797292996192543829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454588881198195330795029219 681883321797292996192543829)
                  ·
                    refine ⟨7990820177312027299131373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 681883321797292996192543829 7990820177312027299131373)
                    ·
                      refine ⟨2996557566492010237174265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7990820177312027299131373 2996557566492010237174265)
                      ·
                        rfl

theorem cell23_5835775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_5835775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835775 prefixEnd_5835775 := by exact prefixLift 5835775
  have htrace : WordTrace (prefixWord ++ tailWord_5835775) baseStart_5835775 baseEnd_5835775 := by
    simpa [prefixWord, tailWord_5835775, baseEnd_5835775] using wordTrace_append hprefix tailTrace_5835775
  have hstable : (prefixWord ++ tailWord_5835775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835775).length < 2 ^ (prefixWord ++ tailWord_5835775).sum := by decide
  have hdescent : baseEnd_5835775 < baseStart_5835775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835785 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_5835785 : Nat := 118140960795 + 5835785 * 2 ^ 59
def prefixEnd_5835785 : Nat := 4983230072969 + 3 ^ 40 * 5835785 * 2
def baseEnd_5835785 : Nat := 2996562701298555198049219

theorem tailTrace_5835785 : CollatzResearch.WordTrace tailWord_5835785 prefixEnd_5835785 2996562701298555198049219 := by
  unfold tailWord_5835785
  simp only [CollatzResearch.WordTrace]
  refine ⟨212848565162955092573940809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141899043441970061715960539 212848565162955092573940809)
  ·
    refine ⟨159636423872216319430455607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212848565162955092573940809 159636423872216319430455607)
    ·
      refine ⟨239454635808324479145683411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159636423872216319430455607 239454635808324479145683411)
      ·
        refine ⟨359181953712486718718525117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239454635808324479145683411 359181953712486718718525117)
        ·
          refine ⟨134693232642182519519446919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359181953712486718718525117 134693232642182519519446919)
          ·
            refine ⟨202039848963273779279170379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134693232642182519519446919 202039848963273779279170379)
            ·
              refine ⟨303059773444910668918755569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202039848963273779279170379 303059773444910668918755569)
              ·
                refine ⟨227294830083683001689066677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303059773444910668918755569 227294830083683001689066677)
                ·
                  refine ⟨21308890320345281408350001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227294830083683001689066677 21308890320345281408350001)
                  ·
                    refine ⟨15981667740258961056262501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21308890320345281408350001 15981667740258961056262501)
                    ·
                      refine ⟨2996562701298555198049219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15981667740258961056262501 2996562701298555198049219)
                      ·
                        rfl

theorem cell23_5835785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_5835785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835785 prefixEnd_5835785 := by exact prefixLift 5835785
  have htrace : WordTrace (prefixWord ++ tailWord_5835785) baseStart_5835785 baseEnd_5835785 := by
    simpa [prefixWord, tailWord_5835785, baseEnd_5835785] using wordTrace_append hprefix tailTrace_5835785
  have hstable : (prefixWord ++ tailWord_5835785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835785).length < 2 ^ (prefixWord ++ tailWord_5835785).sum := by decide
  have hdescent : baseEnd_5835785 < baseStart_5835785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835802 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_5835802 : Nat := 118140960795 + 5835802 * 2 ^ 59
def prefixEnd_5835802 : Nat := 4983230072969 + 3 ^ 40 * 5835802 * 2
def baseEnd_5835802 : Nat := 2996571430469681631536641

theorem tailTrace_5835802 : CollatzResearch.WordTrace tailWord_5835802 prefixEnd_5835802 2996571430469681631536641 := by
  unfold tailWord_5835802
  simp only [CollatzResearch.WordTrace]
  refine ⟨53212296300973376119327415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141899456802595669651539773 53212296300973376119327415)
  ·
    refine ⟨79818444451460064178991123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53212296300973376119327415 79818444451460064178991123)
    ·
      refine ⟨119727666677190096268486685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79818444451460064178991123 119727666677190096268486685)
      ·
        refine ⟨44897875003946286100682507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119727666677190096268486685 44897875003946286100682507)
        ·
          refine ⟨67346812505919429151023761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44897875003946286100682507 67346812505919429151023761)
          ·
            refine ⟨50510109379439571863267821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67346812505919429151023761 50510109379439571863267821)
            ·
              refine ⟨18941291017289839448725433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50510109379439571863267821 18941291017289839448725433)
              ·
                refine ⟨14205968262967379586544075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18941291017289839448725433 14205968262967379586544075)
                ·
                  refine ⟨21308952394451069379816113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14205968262967379586544075 21308952394451069379816113)
                  ·
                    refine ⟨15981714295838302034862085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21308952394451069379816113 15981714295838302034862085)
                    ·
                      refine ⟨2996571430469681631536641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15981714295838302034862085 2996571430469681631536641)
                      ·
                        rfl

theorem cell23_5835802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_5835802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835802 prefixEnd_5835802 := by exact prefixLift 5835802
  have htrace : WordTrace (prefixWord ++ tailWord_5835802) baseStart_5835802 baseEnd_5835802 := by
    simpa [prefixWord, tailWord_5835802, baseEnd_5835802] using wordTrace_append hprefix tailTrace_5835802
  have hstable : (prefixWord ++ tailWord_5835802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835802).length < 2 ^ (prefixWord ++ tailWord_5835802).sum := by decide
  have hdescent : baseEnd_5835802 < baseStart_5835802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835809 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5835809 : Nat := 118140960795 + 5835809 * 2 ^ 59
def prefixEnd_5835809 : Nat := 4983230072969 + 3 ^ 40 * 5835809 * 2
def baseEnd_5835809 : Nat := 2996575024834263104149109

theorem tailTrace_5835809 : CollatzResearch.WordTrace tailWord_5835809 prefixEnd_5835809 2996575024834263104149109 := by
  unfold tailWord_5835809
  simp only [CollatzResearch.WordTrace]
  refine ⟨212849440514868144672814481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141899627009912096448542987 212849440514868144672814481)
  ·
    refine ⟨159637080386151108504610861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212849440514868144672814481 159637080386151108504610861)
    ·
      refine ⟨59863905144806665689229073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159637080386151108504610861 59863905144806665689229073)
      ·
        refine ⟨44897928858604999266921805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59863905144806665689229073 44897928858604999266921805)
        ·
          refine ⟨16836723321976874725095677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44897928858604999266921805 16836723321976874725095677)
          ·
            refine ⟨6313771245741328021910879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16836723321976874725095677 6313771245741328021910879)
            ·
              refine ⟨9470656868611992032866319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313771245741328021910879 9470656868611992032866319)
              ·
                refine ⟨14205985302917988049299479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470656868611992032866319 14205985302917988049299479)
                ·
                  refine ⟨21308977954376982073949219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14205985302917988049299479 21308977954376982073949219)
                  ·
                    refine ⟨31963466931565473110923829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21308977954376982073949219 31963466931565473110923829)
                    ·
                      refine ⟨2996575024834263104149109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31963466931565473110923829 2996575024834263104149109)
                      ·
                        rfl

theorem cell23_5835809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5835809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835809 prefixEnd_5835809 := by exact prefixLift 5835809
  have htrace : WordTrace (prefixWord ++ tailWord_5835809) baseStart_5835809 baseEnd_5835809 := by
    simpa [prefixWord, tailWord_5835809, baseEnd_5835809] using wordTrace_append hprefix tailTrace_5835809
  have hstable : (prefixWord ++ tailWord_5835809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835809).length < 2 ^ (prefixWord ++ tailWord_5835809).sum := by decide
  have hdescent : baseEnd_5835809 < baseStart_5835809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835825 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_5835825 : Nat := 118140960795 + 5835825 * 2 ^ 59
def prefixEnd_5835825 : Nat := 4983230072969 + 3 ^ 40 * 5835825 * 2
def baseEnd_5835825 : Nat := 998861080174911680516345

theorem tailTrace_5835825 : CollatzResearch.WordTrace tailWord_5835825 prefixEnd_5835825 998861080174911680516345 := by
  unfold tailWord_5835825
  simp only [CollatzResearch.WordTrace]
  refine ⟨212850024082810179405396929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141900016055206786270264619 212850024082810179405396929)
  ·
    refine ⟨159637518062107634554047697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212850024082810179405396929 159637518062107634554047697)
    ·
      refine ⟨119728138546580725915535773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159637518062107634554047697 119728138546580725915535773)
      ·
        refine ⟨44898051954967772218325915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119728138546580725915535773 44898051954967772218325915)
        ·
          refine ⟨67347077932451658327488873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44898051954967772218325915 67347077932451658327488873)
          ·
            refine ⟨50510308449338743745616655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67347077932451658327488873 50510308449338743745616655)
            ·
              refine ⟨75765462674008115618424983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50510308449338743745616655 75765462674008115618424983)
              ·
                refine ⟨113648194011012173427637475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75765462674008115618424983 113648194011012173427637475)
                ·
                  refine ⟨170472291016518260141456213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113648194011012173427637475 170472291016518260141456213)
                  ·
                    refine ⟨998861080174911680516345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170472291016518260141456213 998861080174911680516345)
                    ·
                      rfl

theorem cell23_5835825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_5835825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835825 prefixEnd_5835825 := by exact prefixLift 5835825
  have htrace : WordTrace (prefixWord ++ tailWord_5835825) baseStart_5835825 baseEnd_5835825 := by
    simpa [prefixWord, tailWord_5835825, baseEnd_5835825] using wordTrace_append hprefix tailTrace_5835825
  have hstable : (prefixWord ++ tailWord_5835825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835825).length < 2 ^ (prefixWord ++ tailWord_5835825).sum := by decide
  have hdescent : baseEnd_5835825 < baseStart_5835825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835846 : List Nat := [6, 1, 1, 1, 1, 3, 3, 7]
def baseStart_5835846 : Nat := 118140960795 + 5835846 * 2 ^ 59
def prefixEnd_5835846 : Nat := 4983230072969 + 3 ^ 40 * 5835846 * 2
def baseEnd_5835846 : Nat := 110984963837721461458757

theorem tailTrace_5835846 : CollatzResearch.WordTrace tailWord_5835846 prefixEnd_5835846 110984963837721461458757 := by
  unfold tailWord_5835846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651587187991690624747231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141900526677156066661274261 6651587187991690624747231)
  ·
    refine ⟨9977380781987535937120847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6651587187991690624747231 9977380781987535937120847)
    ·
      refine ⟨14966071172981303905681271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9977380781987535937120847 14966071172981303905681271)
      ·
        refine ⟨22449106759471955858521907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14966071172981303905681271 22449106759471955858521907)
        ·
          refine ⟨33673660139207933787782861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22449106759471955858521907 33673660139207933787782861)
          ·
            refine ⟨12627622552202975170418573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33673660139207933787782861 12627622552202975170418573)
            ·
              refine ⟨4735358457076115688906965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12627622552202975170418573 4735358457076115688906965)
              ·
                refine ⟨110984963837721461458757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4735358457076115688906965 110984963837721461458757)
                ·
                  rfl

theorem cell23_5835846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_5835846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835846 prefixEnd_5835846 := by exact prefixLift 5835846
  have htrace : WordTrace (prefixWord ++ tailWord_5835846) baseStart_5835846 baseEnd_5835846 := by
    simpa [prefixWord, tailWord_5835846, baseEnd_5835846] using wordTrace_append hprefix tailTrace_5835846
  have hstable : (prefixWord ++ tailWord_5835846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835846).length < 2 ^ (prefixWord ++ tailWord_5835846).sum := by decide
  have hdescent : baseEnd_5835846 < baseStart_5835846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835855 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 6, 6]
def baseStart_5835855 : Nat := 118140960795 + 5835855 * 2 ^ 59
def prefixEnd_5835855 : Nat := 4983230072969 + 3 ^ 40 * 5835855 * 2
def baseEnd_5835855 : Nat := 998866214981456641391299

theorem tailTrace_5835855 : CollatzResearch.WordTrace tailWord_5835855 prefixEnd_5835855 998866214981456641391299 := by
  unfold tailWord_5835855
  simp only [CollatzResearch.WordTrace]
  refine ⟨212851118272701494528989019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141900745515134329685992679 212851118272701494528989019)
  ·
    refine ⟨319276677409052241793483529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212851118272701494528989019 319276677409052241793483529)
    ·
      refine ⟨239457508056789181345112647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319276677409052241793483529 239457508056789181345112647)
      ·
        refine ⟨359186262085183772017668971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239457508056789181345112647 359186262085183772017668971)
        ·
          refine ⟨538779393127775658026503457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359186262085183772017668971 538779393127775658026503457)
          ·
            refine ⟨404084544845831743519877593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538779393127775658026503457 404084544845831743519877593)
            ·
              refine ⟨303063408634373807639908195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404084544845831743519877593 303063408634373807639908195)
              ·
                refine ⟨454595112951560711459862293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303063408634373807639908195 454595112951560711459862293)
                ·
                  refine ⟨21309145919604408349681045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 454595112951560711459862293 21309145919604408349681045)
                  ·
                    refine ⟨998866214981456641391299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21309145919604408349681045 998866214981456641391299)
                    ·
                      rfl

theorem cell23_5835855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_5835855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835855 prefixEnd_5835855 := by exact prefixLift 5835855
  have htrace : WordTrace (prefixWord ++ tailWord_5835855) baseStart_5835855 baseEnd_5835855 := by
    simpa [prefixWord, tailWord_5835855, baseEnd_5835855] using wordTrace_append hprefix tailTrace_5835855
  have hstable : (prefixWord ++ tailWord_5835855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835855).length < 2 ^ (prefixWord ++ tailWord_5835855).sum := by decide
  have hdescent : baseEnd_5835855 < baseStart_5835855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835896 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_5835896 : Nat := 118140960795 + 5835896 * 2 ^ 59
def prefixEnd_5835896 : Nat := 4983230072969 + 3 ^ 40 * 5835896 * 2
def baseEnd_5835896 : Nat := 2996619697651204263761209

theorem tailTrace_5835896 : CollatzResearch.WordTrace tailWord_5835896 prefixEnd_5835896 2996619697651204263761209 := by
  unfold tailWord_5835896
  simp only [CollatzResearch.WordTrace]
  refine ⟨106426306832776479265615771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141901742443701972354154361 106426306832776479265615771)
  ·
    refine ⟨159639460249164718898423657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106426306832776479265615771 159639460249164718898423657)
    ·
      refine ⟨119729595186873539173817743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159639460249164718898423657 119729595186873539173817743)
      ·
        refine ⟨179594392780310308760726615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119729595186873539173817743 179594392780310308760726615)
        ·
          refine ⟨269391589170465463141089923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179594392780310308760726615 269391589170465463141089923)
          ·
            refine ⟨404087383755698194711634885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269391589170465463141089923 404087383755698194711634885)
            ·
              refine ⟨75766384454193411508431541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404087383755698194711634885 75766384454193411508431541)
              ·
                refine ⟨7103098542580632328915457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75766384454193411508431541 7103098542580632328915457)
                ·
                  refine ⟨5327323906935474246686593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7103098542580632328915457 5327323906935474246686593)
                  ·
                    refine ⟨3995492930201605685014945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5327323906935474246686593 3995492930201605685014945)
                    ·
                      refine ⟨2996619697651204263761209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995492930201605685014945 2996619697651204263761209)
                      ·
                        rfl

theorem cell23_5835896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_5835896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835896 prefixEnd_5835896 := by exact prefixLift 5835896
  have htrace : WordTrace (prefixWord ++ tailWord_5835896) baseStart_5835896 baseEnd_5835896 := by
    simpa [prefixWord, tailWord_5835896, baseEnd_5835896] using wordTrace_append hprefix tailTrace_5835896
  have hstable : (prefixWord ++ tailWord_5835896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835896).length < 2 ^ (prefixWord ++ tailWord_5835896).sum := by decide
  have hdescent : baseEnd_5835896 < baseStart_5835896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835936 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 5]
def baseStart_5835936 : Nat := 118140960795 + 5835936 * 2 ^ 59
def prefixEnd_5835936 : Nat := 4983230072969 + 3 ^ 40 * 5835936 * 2
def baseEnd_5835936 : Nat := 332960026319709345251225

theorem tailTrace_5835936 : CollatzResearch.WordTrace tailWord_5835936 prefixEnd_5835936 332960026319709345251225 := by
  unfold tailWord_5835936
  simp only [CollatzResearch.WordTrace]
  refine ⟨106427036292704022681343831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141902715056938696908458441 106427036292704022681343831)
  ·
    refine ⟨159640554439056034022015747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106427036292704022681343831 159640554439056034022015747)
    ·
      refine ⟨239460831658584051033023621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159640554439056034022015747 239460831658584051033023621)
      ·
        refine ⟨44898905935984509568691929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239460831658584051033023621 44898905935984509568691929)
        ·
          refine ⟨33674179451988382176518947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44898905935984509568691929 33674179451988382176518947)
          ·
            refine ⟨50511269177982573264778421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33674179451988382176518947 50511269177982573264778421)
            ·
              refine ⟨4735431485435866243572977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50511269177982573264778421 4735431485435866243572977)
              ·
                refine ⟨3551573614076899682679733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735431485435866243572977 3551573614076899682679733)
                ·
                  refine ⟨332960026319709345251225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3551573614076899682679733 332960026319709345251225)
                  ·
                    rfl

theorem cell23_5835936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 5].length) (baseStart_5835936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835936 prefixEnd_5835936 := by exact prefixLift 5835936
  have htrace : WordTrace (prefixWord ++ tailWord_5835936) baseStart_5835936 baseEnd_5835936 := by
    simpa [prefixWord, tailWord_5835936, baseEnd_5835936] using wordTrace_append hprefix tailTrace_5835936
  have hstable : (prefixWord ++ tailWord_5835936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835936).length < 2 ^ (prefixWord ++ tailWord_5835936).sum := by decide
  have hdescent : baseEnd_5835936 < baseStart_5835936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835966 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5835966 : Nat := 118140960795 + 5835966 * 2 ^ 59
def prefixEnd_5835966 : Nat := 4983230072969 + 3 ^ 40 * 5835966 * 2
def baseEnd_5835966 : Nat := 998885213765672996628629

theorem tailTrace_5835966 : CollatzResearch.WordTrace tailWord_5835966 prefixEnd_5835966 998885213765672996628629 := by
  unfold tailWord_5835966
  simp only [CollatzResearch.WordTrace]
  refine ⟨26606895846912420060784969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141903444516866240324186501 26606895846912420060784969)
  ·
    refine ⟨19955171885184315045588727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26606895846912420060784969 19955171885184315045588727)
    ·
      refine ⟨29932757827776472568383091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19955171885184315045588727 29932757827776472568383091)
      ·
        refine ⟨44899136741664708852574637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29932757827776472568383091 44899136741664708852574637)
        ·
          refine ⟨16837176278124265819715489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44899136741664708852574637 16837176278124265819715489)
          ·
            refine ⟨12627882208593199364786617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16837176278124265819715489 12627882208593199364786617)
            ·
              refine ⟨9470911656444899523589963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12627882208593199364786617 9470911656444899523589963)
              ·
                refine ⟨14206367484667349285384945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470911656444899523589963 14206367484667349285384945)
                ·
                  refine ⟨10654775613500511964038709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14206367484667349285384945 10654775613500511964038709)
                  ·
                    refine ⟨998885213765672996628629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10654775613500511964038709 998885213765672996628629)
                    ·
                      rfl

theorem cell23_5835966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5835966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835966 prefixEnd_5835966 := by exact prefixLift 5835966
  have htrace : WordTrace (prefixWord ++ tailWord_5835966) baseStart_5835966 baseEnd_5835966 := by
    simpa [prefixWord, tailWord_5835966, baseEnd_5835966] using wordTrace_append hprefix tailTrace_5835966
  have hstable : (prefixWord ++ tailWord_5835966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835966).length < 2 ^ (prefixWord ++ tailWord_5835966).sum := by decide
  have hdescent : baseEnd_5835966 < baseStart_5835966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5835986 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_5835986 : Nat := 118140960795 + 5835986 * 2 ^ 59
def prefixEnd_5835986 : Nat := 4983230072969 + 3 ^ 40 * 5835986 * 2
def baseEnd_5835986 : Nat := 2996665910910108911635795

theorem tailTrace_5835986 : CollatzResearch.WordTrace tailWord_5835986 prefixEnd_5835986 2996665910910108911635795 := by
  unfold tailWord_5835986
  simp only [CollatzResearch.WordTrace]
  refine ⟨53213974058806725975501953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141903930823484602601338541 53213974058806725975501953)
  ·
    refine ⟨39910480544105044481626465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53213974058806725975501953 39910480544105044481626465)
    ·
      refine ⟨29932860408078783361219849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39910480544105044481626465 29932860408078783361219849)
      ·
        refine ⟨22449645306059087520914887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29932860408078783361219849 22449645306059087520914887)
        ·
          refine ⟨33674467959088631281372331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22449645306059087520914887 33674467959088631281372331)
          ·
            refine ⟨50511701938632946922058497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33674467959088631281372331 50511701938632946922058497)
            ·
              refine ⟨37883776453974710191543873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50511701938632946922058497 37883776453974710191543873)
              ·
                refine ⟨28412832340481032643657905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37883776453974710191543873 28412832340481032643657905)
                ·
                  refine ⟨21309624255360774482743429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28412832340481032643657905 21309624255360774482743429)
                  ·
                    refine ⟨3995554547880145215514393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21309624255360774482743429 3995554547880145215514393)
                    ·
                      refine ⟨2996665910910108911635795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995554547880145215514393 2996665910910108911635795)
                      ·
                        rfl

theorem cell23_5835986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_5835986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5835986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5835986 prefixEnd_5835986 := by exact prefixLift 5835986
  have htrace : WordTrace (prefixWord ++ tailWord_5835986) baseStart_5835986 baseEnd_5835986 := by
    simpa [prefixWord, tailWord_5835986, baseEnd_5835986] using wordTrace_append hprefix tailTrace_5835986
  have hstable : (prefixWord ++ tailWord_5835986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5835986).length < 2 ^ (prefixWord ++ tailWord_5835986).sum := by decide
  have hdescent : baseEnd_5835986 < baseStart_5835986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5835986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836020 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5836020 : Nat := 118140960795 + 5836020 * 2 ^ 59
def prefixEnd_5836020 : Nat := 4983230072969 + 3 ^ 40 * 5836020 * 2
def baseEnd_5836020 : Nat := 2996683369252361778610639

theorem tailTrace_5836020 : CollatzResearch.WordTrace tailWord_5836020 prefixEnd_5836020 2996683369252361778610639 := by
  unfold tailWord_5836020
  simp only [CollatzResearch.WordTrace]
  refine ⟨106428568158551863854372757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141904757544735818472497009 106428568158551863854372757)
  ·
    refine ⟨4988839132432118618173723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106428568158551863854372757 4988839132432118618173723)
    ·
      refine ⟨7483258698648177927260585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988839132432118618173723 7483258698648177927260585)
      ·
        refine ⟨5612444023986133445445439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7483258698648177927260585 5612444023986133445445439)
        ·
          refine ⟨8418666035979200168168159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612444023986133445445439 8418666035979200168168159)
          ·
            refine ⟨12627999053968800252252239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418666035979200168168159 12627999053968800252252239)
            ·
              refine ⟨18941998580953200378378359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627999053968800252252239 18941998580953200378378359)
              ·
                refine ⟨28412997871429800567567539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18941998580953200378378359 28412997871429800567567539)
                ·
                  refine ⟨42619496807144700851351309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28412997871429800567567539 42619496807144700851351309)
                  ·
                    refine ⟨15982311302679262819256741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42619496807144700851351309 15982311302679262819256741)
                    ·
                      refine ⟨2996683369252361778610639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15982311302679262819256741 2996683369252361778610639)
                      ·
                        rfl

theorem cell23_5836020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5836020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836020 prefixEnd_5836020 := by exact prefixLift 5836020
  have htrace : WordTrace (prefixWord ++ tailWord_5836020) baseStart_5836020 baseEnd_5836020 := by
    simpa [prefixWord, tailWord_5836020, baseEnd_5836020] using wordTrace_append hprefix tailTrace_5836020
  have hstable : (prefixWord ++ tailWord_5836020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836020).length < 2 ^ (prefixWord ++ tailWord_5836020).sum := by decide
  have hdescent : baseEnd_5836020 < baseStart_5836020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836030 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5836030 : Nat := 118140960795 + 5836030 * 2 ^ 59
def prefixEnd_5836030 : Nat := 4983230072969 + 3 ^ 40 * 5836030 * 2
def baseEnd_5836030 : Nat := 998896168019635579828531

theorem tailTrace_5836030 : CollatzResearch.WordTrace tailWord_5836030 prefixEnd_5836030 998896168019635579828531 := by
  unfold tailWord_5836030
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607187630883437427076193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141905000698044999611073029 26607187630883437427076193)
  ·
    refine ⟨19955390723162578070307145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26607187630883437427076193 19955390723162578070307145)
    ·
      refine ⟨14966543042371933552730359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19955390723162578070307145 14966543042371933552730359)
      ·
        refine ⟨22449814563557900329095539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14966543042371933552730359 22449814563557900329095539)
        ·
          refine ⟨33674721845336850493643309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22449814563557900329095539 33674721845336850493643309)
          ·
            refine ⟨12628020692001318935116241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33674721845336850493643309 12628020692001318935116241)
            ·
              refine ⟨9471015519000989201337181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12628020692001318935116241 9471015519000989201337181)
              ·
                refine ⟨3551630819625370950501443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9471015519000989201337181 3551630819625370950501443)
                ·
                  refine ⟨5327446229438056425752165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551630819625370950501443 5327446229438056425752165)
                  ·
                    refine ⟨998896168019635579828531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327446229438056425752165 998896168019635579828531)
                    ·
                      rfl

theorem cell23_5836030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5836030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836030 prefixEnd_5836030 := by exact prefixLift 5836030
  have htrace : WordTrace (prefixWord ++ tailWord_5836030) baseStart_5836030 baseEnd_5836030 := by
    simpa [prefixWord, tailWord_5836030, baseEnd_5836030] using wordTrace_append hprefix tailTrace_5836030
  have hstable : (prefixWord ++ tailWord_5836030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836030).length < 2 ^ (prefixWord ++ tailWord_5836030).sum := by decide
  have hdescent : baseEnd_5836030 < baseStart_5836030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836032 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_5836032 : Nat := 118140960795 + 5836032 * 2 ^ 59
def prefixEnd_5836032 : Nat := 4983230072969 + 3 ^ 40 * 5836032 * 2
def baseEnd_5836032 : Nat := 2996689531020215731660583

theorem tailTrace_5836032 : CollatzResearch.WordTrace tailWord_5836032 prefixEnd_5836032 2996689531020215731660583 := by
  unfold tailWord_5836032
  simp only [CollatzResearch.WordTrace]
  refine ⟨106428786996530126879091175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141905049328706835838788233 106428786996530126879091175)
  ·
    refine ⟨159643180494795190318636763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106428786996530126879091175 159643180494795190318636763)
    ·
      refine ⟨239464770742192785477955145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159643180494795190318636763 239464770742192785477955145)
      ·
        refine ⟨179598578056644589108466359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239464770742192785477955145 179598578056644589108466359)
        ·
          refine ⟨269397867084966883662699539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179598578056644589108466359 269397867084966883662699539)
          ·
            refine ⟨404096800627450325494049309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269397867084966883662699539 404096800627450325494049309)
            ·
              refine ⟨151536300235293872060268491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404096800627450325494049309 151536300235293872060268491)
              ·
                refine ⟨227304450352940808090402737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151536300235293872060268491 227304450352940808090402737)
                ·
                  refine ⟨170478337764705606067802053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227304450352940808090402737 170478337764705606067802053)
                  ·
                    refine ⟨31964688330882301137712885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170478337764705606067802053 31964688330882301137712885)
                    ·
                      refine ⟨2996689531020215731660583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31964688330882301137712885 2996689531020215731660583)
                      ·
                        rfl

theorem cell23_5836032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_5836032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836032 prefixEnd_5836032 := by exact prefixLift 5836032
  have htrace : WordTrace (prefixWord ++ tailWord_5836032) baseStart_5836032 baseEnd_5836032 := by
    simpa [prefixWord, tailWord_5836032, baseEnd_5836032] using wordTrace_append hprefix tailTrace_5836032
  have hstable : (prefixWord ++ tailWord_5836032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836032).length < 2 ^ (prefixWord ++ tailWord_5836032).sum := by decide
  have hdescent : baseEnd_5836032 < baseStart_5836032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836096 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_5836096 : Nat := 118140960795 + 5836096 * 2 ^ 59
def prefixEnd_5836096 : Nat := 4983230072969 + 3 ^ 40 * 5836096 * 2
def baseEnd_5836096 : Nat := 2996722393782103481260289

theorem tailTrace_5836096 : CollatzResearch.WordTrace tailWord_5836096 prefixEnd_5836096 2996722393782103481260289 := by
  unfold tailWord_5836096
  simp only [CollatzResearch.WordTrace]
  refine ⟨106429954132414196344256071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141906605509885595125674761 106429954132414196344256071)
  ·
    refine ⟨159644931198621294516384107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106429954132414196344256071 159644931198621294516384107)
    ·
      refine ⟨239467396797931941774576161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159644931198621294516384107 239467396797931941774576161)
      ·
        refine ⟨179600547598448956330932121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239467396797931941774576161 179600547598448956330932121)
        ·
          refine ⟨134700410698836717248199091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179600547598448956330932121 134700410698836717248199091)
          ·
            refine ⟨202050616048255075872298637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134700410698836717248199091 202050616048255075872298637)
            ·
              refine ⟨75768981018095653452111989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202050616048255075872298637 75768981018095653452111989)
              ·
                refine ⟨7103341970446467511135499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75768981018095653452111989 7103341970446467511135499)
                ·
                  refine ⟨10655012955669701266703249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103341970446467511135499 10655012955669701266703249)
                  ·
                    refine ⟨7991259716752275950027437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10655012955669701266703249 7991259716752275950027437)
                    ·
                      refine ⟨2996722393782103481260289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7991259716752275950027437 2996722393782103481260289)
                      ·
                        rfl

theorem cell23_5836096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_5836096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836096 prefixEnd_5836096 := by exact prefixLift 5836096
  have htrace : WordTrace (prefixWord ++ tailWord_5836096) baseStart_5836096 baseEnd_5836096 := by
    simpa [prefixWord, tailWord_5836096, baseEnd_5836096] using wordTrace_append hprefix tailTrace_5836096
  have hstable : (prefixWord ++ tailWord_5836096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836096).length < 2 ^ (prefixWord ++ tailWord_5836096).sum := by decide
  have hdescent : baseEnd_5836096 < baseStart_5836096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836153 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 1, 3, 2]
def baseStart_5836153 : Nat := 118140960795 + 5836153 * 2 ^ 59
def prefixEnd_5836153 : Nat := 4983230072969 + 3 ^ 40 * 5836153 * 2
def baseEnd_5836153 : Nat := 2996751662179409758247527

theorem tailTrace_5836153 : CollatzResearch.WordTrace tailWord_5836153 prefixEnd_5836153 2996751662179409758247527 := by
  unfold tailWord_5836153
  simp only [CollatzResearch.WordTrace]
  refine ⟨212861987225621891423337113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141907991483747927615558075 212861987225621891423337113)
  ·
    refine ⟨159646490419216418567502835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212861987225621891423337113 159646490419216418567502835)
    ·
      refine ⟨239469735628824627851254253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159646490419216418567502835 239469735628824627851254253)
      ·
        refine ⟨89801150860809235444220345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239469735628824627851254253 89801150860809235444220345)
        ·
          refine ⟨67350863145606926583165259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89801150860809235444220345 67350863145606926583165259)
          ·
            refine ⟨101026294718410389874747889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67350863145606926583165259 101026294718410389874747889)
            ·
              refine ⟨75769721038807792406060917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101026294718410389874747889 75769721038807792406060917)
              ·
                refine ⟨7103411347388230538068211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75769721038807792406060917 7103411347388230538068211)
                ·
                  refine ⟨10655117021082345807102317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103411347388230538068211 10655117021082345807102317)
                  ·
                    refine ⟨3995668882905879677663369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10655117021082345807102317 3995668882905879677663369)
                    ·
                      refine ⟨2996751662179409758247527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995668882905879677663369 2996751662179409758247527)
                      ·
                        rfl

theorem cell23_5836153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_5836153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836153 prefixEnd_5836153 := by exact prefixLift 5836153
  have htrace : WordTrace (prefixWord ++ tailWord_5836153) baseStart_5836153 baseEnd_5836153 := by
    simpa [prefixWord, tailWord_5836153, baseEnd_5836153] using wordTrace_append hprefix tailTrace_5836153
  have hstable : (prefixWord ++ tailWord_5836153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836153).length < 2 ^ (prefixWord ++ tailWord_5836153).sum := by decide
  have hdescent : baseEnd_5836153 < baseStart_5836153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836161 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5836161 : Nat := 118140960795 + 5836161 * 2 ^ 59
def prefixEnd_5836161 : Nat := 4983230072969 + 3 ^ 40 * 5836161 * 2
def baseEnd_5836161 : Nat := 2996755770024645726947491

theorem tailTrace_5836161 : CollatzResearch.WordTrace tailWord_5836161 prefixEnd_5836161 2996755770024645726947491 := by
  unfold tailWord_5836161
  simp only [CollatzResearch.WordTrace]
  refine ⟨212862279009592908789628337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141908186006395272526418891 212862279009592908789628337)
  ·
    refine ⟨159646709257194681592221253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212862279009592908789628337 159646709257194681592221253)
    ·
      refine ⟨29933757985724002798541485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159646709257194681592221253 29933757985724002798541485)
      ·
        refine ⟨11225159244646501049453057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29933757985724002798541485 11225159244646501049453057)
        ·
          refine ⟨8418869433484875787089793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11225159244646501049453057 8418869433484875787089793)
          ·
            refine ⟨6314152075113656840317345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8418869433484875787089793 6314152075113656840317345)
            ·
              refine ⟨4735614056335242630238009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6314152075113656840317345 4735614056335242630238009)
              ·
                refine ⟨3551710542251431972678507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735614056335242630238009 3551710542251431972678507)
                ·
                  refine ⟨5327565813377147959017761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551710542251431972678507 5327565813377147959017761)
                  ·
                    refine ⟨3995674360032860969263321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5327565813377147959017761 3995674360032860969263321)
                    ·
                      refine ⟨2996755770024645726947491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995674360032860969263321 2996755770024645726947491)
                      ·
                        rfl

theorem cell23_5836161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5836161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836161 prefixEnd_5836161 := by exact prefixLift 5836161
  have htrace : WordTrace (prefixWord ++ tailWord_5836161) baseStart_5836161 baseEnd_5836161 := by
    simpa [prefixWord, tailWord_5836161, baseEnd_5836161] using wordTrace_append hprefix tailTrace_5836161
  have hstable : (prefixWord ++ tailWord_5836161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836161).length < 2 ^ (prefixWord ++ tailWord_5836161).sum := by decide
  have hdescent : baseEnd_5836161 < baseStart_5836161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836183 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_5836183 : Nat := 118140960795 + 5836183 * 2 ^ 59
def prefixEnd_5836183 : Nat := 4983230072969 + 3 ^ 40 * 5836183 * 2
def baseEnd_5836183 : Nat := 2996767066599044640872389

theorem tailTrace_5836183 : CollatzResearch.WordTrace tailWord_5836183 prefixEnd_5836183 2996767066599044640872389 := by
  unfold tailWord_5836183
  simp only [CollatzResearch.WordTrace]
  refine ⟨212863081415513206546929203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141908720943675471031286135 212863081415513206546929203)
  ·
    refine ⟨319294622123269809820393805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212863081415513206546929203 319294622123269809820393805)
    ·
      refine ⟨119735483296226178682647677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319294622123269809820393805 119735483296226178682647677)
      ·
        refine ⟨44900806236084817005992879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119735483296226178682647677 44900806236084817005992879)
        ·
          refine ⟨67351209354127225508989319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44900806236084817005992879 67351209354127225508989319)
          ·
            refine ⟨101026814031190838263483979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67351209354127225508989319 101026814031190838263483979)
            ·
              refine ⟨151540221046786257395225969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101026814031190838263483979 151540221046786257395225969)
              ·
                refine ⟨113655165785089693046419477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151540221046786257395225969 113655165785089693046419477)
                ·
                  refine ⟨5327585896176079361550913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113655165785089693046419477 5327585896176079361550913)
                  ·
                    refine ⟨3995689422132059521163185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5327585896176079361550913 3995689422132059521163185)
                    ·
                      refine ⟨2996767066599044640872389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995689422132059521163185 2996767066599044640872389)
                      ·
                        rfl

theorem cell23_5836183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_5836183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836183 prefixEnd_5836183 := by exact prefixLift 5836183
  have htrace : WordTrace (prefixWord ++ tailWord_5836183) baseStart_5836183 baseEnd_5836183 := by
    simpa [prefixWord, tailWord_5836183, baseEnd_5836183] using wordTrace_append hprefix tailTrace_5836183
  have hstable : (prefixWord ++ tailWord_5836183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836183).length < 2 ^ (prefixWord ++ tailWord_5836183).sum := by decide
  have hdescent : baseEnd_5836183 < baseStart_5836183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836186 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5836186 : Nat := 118140960795 + 5836186 * 2 ^ 59
def prefixEnd_5836186 : Nat := 4983230072969 + 3 ^ 40 * 5836186 * 2
def baseEnd_5836186 : Nat := 2996768607041008129134875

theorem tailTrace_5836186 : CollatzResearch.WordTrace tailWord_5836186 prefixEnd_5836186 2996768607041008129134875 := by
  unfold tailWord_5836186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53215797708625584514822103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141908793889668225372858941 53215797708625584514822103)
  ·
    refine ⟨79823696562938376772233155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53215797708625584514822103 79823696562938376772233155)
    ·
      refine ⟨119735544844407565158349733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79823696562938376772233155 119735544844407565158349733)
      ·
        refine ⟨22450414658326418467190575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119735544844407565158349733 22450414658326418467190575)
        ·
          refine ⟨33675621987489627700785863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22450414658326418467190575 33675621987489627700785863)
          ·
            refine ⟨50513432981234441551178795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33675621987489627700785863 50513432981234441551178795)
            ·
              refine ⟨75770149471851662326768193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50513432981234441551178795 75770149471851662326768193)
              ·
                refine ⟨56827612103888746745076145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75770149471851662326768193 56827612103888746745076145)
                ·
                  refine ⟨42620709077916560058807109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56827612103888746745076145 42620709077916560058807109)
                  ·
                    refine ⟨7991382952109355011026333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42620709077916560058807109 7991382952109355011026333)
                    ·
                      refine ⟨2996768607041008129134875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7991382952109355011026333 2996768607041008129134875)
                      ·
                        rfl

theorem cell23_5836186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5836186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836186 prefixEnd_5836186 := by exact prefixLift 5836186
  have htrace : WordTrace (prefixWord ++ tailWord_5836186) baseStart_5836186 baseEnd_5836186 := by
    simpa [prefixWord, tailWord_5836186, baseEnd_5836186] using wordTrace_append hprefix tailTrace_5836186
  have hstable : (prefixWord ++ tailWord_5836186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836186).length < 2 ^ (prefixWord ++ tailWord_5836186).sum := by decide
  have hdescent : baseEnd_5836186 < baseStart_5836186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836216 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_5836216 : Nat := 118140960795 + 5836216 * 2 ^ 59
def prefixEnd_5836216 : Nat := 4983230072969 + 3 ^ 40 * 5836216 * 2
def baseEnd_5836216 : Nat := 2996784011460643011759737

theorem tailTrace_5836216 : CollatzResearch.WordTrace tailWord_5836216 prefixEnd_5836216 2996784011460643011759737 := by
  unfold tailWord_5836216
  simp only [CollatzResearch.WordTrace]
  refine ⟨106432142512196826591440251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141909523349595768788587001 106432142512196826591440251)
  ·
    refine ⟨159648213768295239887160377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106432142512196826591440251 159648213768295239887160377)
    ·
      refine ⟨119736160326221429915370283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159648213768295239887160377 119736160326221429915370283)
      ·
        refine ⟨179604240489332144873055425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119736160326221429915370283 179604240489332144873055425)
        ·
          refine ⟨134703180366999108654791569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179604240489332144873055425 134703180366999108654791569)
          ·
            refine ⟨101027385275249331491093677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134703180366999108654791569 101027385275249331491093677)
            ·
              refine ⟨37885269478218499309160129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101027385275249331491093677 37885269478218499309160129)
              ·
                refine ⟨28413952108663874481870097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37885269478218499309160129 28413952108663874481870097)
                ·
                  refine ⟨21310464081497905861402573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28413952108663874481870097 21310464081497905861402573)
                  ·
                    refine ⟨7991424030561714698025965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21310464081497905861402573 7991424030561714698025965)
                    ·
                      refine ⟨2996784011460643011759737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7991424030561714698025965 2996784011460643011759737)
                      ·
                        rfl

theorem cell23_5836216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_5836216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836216 prefixEnd_5836216 := by exact prefixLift 5836216
  have htrace : WordTrace (prefixWord ++ tailWord_5836216) baseStart_5836216 baseEnd_5836216 := by
    simpa [prefixWord, tailWord_5836216, baseEnd_5836216] using wordTrace_append hprefix tailTrace_5836216
  have hstable : (prefixWord ++ tailWord_5836216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836216).length < 2 ^ (prefixWord ++ tailWord_5836216).sum := by decide
  have hdescent : baseEnd_5836216 < baseStart_5836216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836236 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_5836236 : Nat := 118140960795 + 5836236 * 2 ^ 59
def prefixEnd_5836236 : Nat := 4983230072969 + 3 ^ 40 * 5836236 * 2
def baseEnd_5836236 : Nat := 998931427024577644503215

theorem tailTrace_5836236 : CollatzResearch.WordTrace tailWord_5836236 prefixEnd_5836236 998931427024577644503215 := by
  unfold tailWord_5836236
  simp only [CollatzResearch.WordTrace]
  refine ⟨106432507242160598299304281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141910009656214131065739041 106432507242160598299304281)
  ·
    refine ⟨79824380431620448724478211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106432507242160598299304281 79824380431620448724478211)
    ·
      refine ⟨119736570647430673086717317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79824380431620448724478211 119736570647430673086717317)
      ·
        refine ⟨22450606996393251203759497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119736570647430673086717317 22450606996393251203759497)
        ·
          refine ⟨16837955247294938402819623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22450606996393251203759497 16837955247294938402819623)
          ·
            refine ⟨25256932870942407604229435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16837955247294938402819623 25256932870942407604229435)
            ·
              refine ⟨37885399306413611406344153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25256932870942407604229435 37885399306413611406344153)
              ·
                refine ⟨28414049479810208554758115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37885399306413611406344153 28414049479810208554758115)
                ·
                  refine ⟨42621074219715312832137173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28414049479810208554758115 42621074219715312832137173)
                  ·
                    refine ⟨998931427024577644503215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42621074219715312832137173 998931427024577644503215)
                    ·
                      rfl

theorem cell23_5836236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_5836236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836236 prefixEnd_5836236 := by exact prefixLift 5836236
  have htrace : WordTrace (prefixWord ++ tailWord_5836236) baseStart_5836236 baseEnd_5836236 := by
    simpa [prefixWord, tailWord_5836236, baseEnd_5836236] using wordTrace_append hprefix tailTrace_5836236
  have hstable : (prefixWord ++ tailWord_5836236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836236).length < 2 ^ (prefixWord ++ tailWord_5836236).sum := by decide
  have hdescent : baseEnd_5836236 < baseStart_5836236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836273 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_5836273 : Nat := 118140960795 + 5836273 * 2 ^ 59
def prefixEnd_5836273 : Nat := 4983230072969 + 3 ^ 40 * 5836273 * 2
def baseEnd_5836273 : Nat := 2996813279857949288746975

theorem tailTrace_5836273 : CollatzResearch.WordTrace tailWord_5836273 prefixEnd_5836273 2996813279857949288746975 := by
  unfold tailWord_5836273
  simp only [CollatzResearch.WordTrace]
  refine ⟨212866363985187151917705473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141910909323458101278470315 212866363985187151917705473)
  ·
    refine ⟨159649772988890363938279105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212866363985187151917705473 159649772988890363938279105)
    ·
      refine ⟨119737329741667772953709329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159649772988890363938279105 119737329741667772953709329)
      ·
        refine ⟨89802997306250829715281997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119737329741667772953709329 89802997306250829715281997)
        ·
          refine ⟨33676123989844061143230749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89802997306250829715281997 33676123989844061143230749)
          ·
            refine ⟨12628546496191522928711531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33676123989844061143230749 12628546496191522928711531)
            ·
              refine ⟨18942819744287284393067297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12628546496191522928711531 18942819744287284393067297)
              ·
                refine ⟨14207114808215463294800473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18942819744287284393067297 14207114808215463294800473)
                ·
                  refine ⟨10655336106161597471100355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14207114808215463294800473 10655336106161597471100355)
                  ·
                    refine ⟨15983004159242396206650533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10655336106161597471100355 15983004159242396206650533)
                    ·
                      refine ⟨2996813279857949288746975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15983004159242396206650533 2996813279857949288746975)
                      ·
                        rfl

theorem cell23_5836273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_5836273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836273 prefixEnd_5836273 := by exact prefixLift 5836273
  have htrace : WordTrace (prefixWord ++ tailWord_5836273) baseStart_5836273 baseEnd_5836273 := by
    simpa [prefixWord, tailWord_5836273, baseEnd_5836273] using wordTrace_append hprefix tailTrace_5836273
  have hstable : (prefixWord ++ tailWord_5836273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836273).length < 2 ^ (prefixWord ++ tailWord_5836273).sum := by decide
  have hdescent : baseEnd_5836273 < baseStart_5836273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836334 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_5836334 : Nat := 118140960795 + 5836334 * 2 ^ 59
def prefixEnd_5836334 : Nat := 4983230072969 + 3 ^ 40 * 5836334 * 2
def baseEnd_5836334 : Nat := 998948200725957850028065

theorem tailTrace_5836334 : CollatzResearch.WordTrace tailWord_5836334 prefixEnd_5836334 998948200725957850028065 := by
  unfold tailWord_5836334
  simp only [CollatzResearch.WordTrace]
  refine ⟨26608573604745769916959507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141912392558644106223784037 26608573604745769916959507)
  ·
    refine ⟨39912860407118654875439261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26608573604745769916959507 39912860407118654875439261)
    ·
      refine ⟨14967322652669495578289723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39912860407118654875439261 14967322652669495578289723)
      ·
        refine ⟨22450983979004243367434585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14967322652669495578289723 22450983979004243367434585)
        ·
          refine ⟨16838237984253182525575939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22450983979004243367434585 16838237984253182525575939)
          ·
            refine ⟨25257356976379773788363909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16838237984253182525575939 25257356976379773788363909)
            ·
              refine ⟨4735754433071207585318233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25257356976379773788363909 4735754433071207585318233)
              ·
                refine ⟨3551815824803405688988675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735754433071207585318233 3551815824803405688988675)
                ·
                  refine ⟨5327723737205108533483013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551815824803405688988675 5327723737205108533483013)
                  ·
                    refine ⟨998948200725957850028065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327723737205108533483013 998948200725957850028065)
                    ·
                      rfl

theorem cell23_5836334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_5836334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836334 prefixEnd_5836334 := by exact prefixLift 5836334
  have htrace : WordTrace (prefixWord ++ tailWord_5836334) baseStart_5836334 baseEnd_5836334 := by
    simpa [prefixWord, tailWord_5836334, baseEnd_5836334] using wordTrace_append hprefix tailTrace_5836334
  have hstable : (prefixWord ++ tailWord_5836334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836334).length < 2 ^ (prefixWord ++ tailWord_5836334).sum := by decide
  have hdescent : baseEnd_5836334 < baseStart_5836334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836363 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 4]
def baseStart_5836363 : Nat := 118140960795 + 5836363 * 2 ^ 59
def prefixEnd_5836363 : Nat := 4983230072969 + 3 ^ 40 * 5836363 * 2
def baseEnd_5836363 : Nat := 2996859493116853936621561

theorem tailTrace_5836363 : CollatzResearch.WordTrace tailWord_5836363 prefixEnd_5836363 2996859493116853936621561 := by
  unfold tailWord_5836363
  simp only [CollatzResearch.WordTrace]
  refine ⟨212869646554861097288481743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141913097703240731525654495 212869646554861097288481743)
  ·
    refine ⟨319304469832291645932722615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212869646554861097288481743 319304469832291645932722615)
    ·
      refine ⟨478956704748437468899083923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319304469832291645932722615 478956704748437468899083923)
      ·
        refine ⟨718435057122656203348625885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478956704748437468899083923 718435057122656203348625885)
        ·
          refine ⟨269413146420996076255734707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 718435057122656203348625885 269413146420996076255734707)
          ·
            refine ⟨404119719631494114383602061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269413146420996076255734707 404119719631494114383602061)
            ·
              refine ⟨151544894861810292893850773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404119719631494114383602061 151544894861810292893850773)
              ·
                refine ⟨7103666946647357479399255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151544894861810292893850773 7103666946647357479399255)
                ·
                  refine ⟨10655500419971036219098883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103666946647357479399255 10655500419971036219098883)
                  ·
                    refine ⟨15983250629956554328648325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10655500419971036219098883 15983250629956554328648325)
                    ·
                      refine ⟨2996859493116853936621561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15983250629956554328648325 2996859493116853936621561)
                      ·
                        rfl

theorem cell23_5836363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 4].length) (baseStart_5836363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836363 prefixEnd_5836363 := by exact prefixLift 5836363
  have htrace : WordTrace (prefixWord ++ tailWord_5836363) baseStart_5836363 baseEnd_5836363 := by
    simpa [prefixWord, tailWord_5836363, baseEnd_5836363] using wordTrace_append hprefix tailTrace_5836363
  have hstable : (prefixWord ++ tailWord_5836363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836363).length < 2 ^ (prefixWord ++ tailWord_5836363).sum := by decide
  have hdescent : baseEnd_5836363 < baseStart_5836363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836373 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_5836373 : Nat := 118140960795 + 5836373 * 2 ^ 59
def prefixEnd_5836373 : Nat := 4983230072969 + 3 ^ 40 * 5836373 * 2
def baseEnd_5836373 : Nat := 998954875974466299165505

theorem tailTrace_5836373 : CollatzResearch.WordTrace tailWord_5836373 prefixEnd_5836373 998954875974466299165505 := by
  unfold tailWord_5836373
  simp only [CollatzResearch.WordTrace]
  refine ⟨212870011284824868996345773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141913340856549912664230515 212870011284824868996345773)
  ·
    refine ⟨79826254231809325873629665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212870011284824868996345773 79826254231809325873629665)
    ·
      refine ⟨59869690673856994405222249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79826254231809325873629665 59869690673856994405222249)
      ·
        refine ⟨44902268005392745803916687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59869690673856994405222249 44902268005392745803916687)
        ·
          refine ⟨67353402008089118705875031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44902268005392745803916687 67353402008089118705875031)
          ·
            refine ⟨101030103012133678058812547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67353402008089118705875031 101030103012133678058812547)
            ·
              refine ⟨151545154518200517088218821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101030103012133678058812547 151545154518200517088218821)
              ·
                refine ⟨28414716472162596954041029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151545154518200517088218821 28414716472162596954041029)
                ·
                  refine ⟨5327759338530486928882693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28414716472162596954041029 5327759338530486928882693)
                  ·
                    refine ⟨998954875974466299165505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327759338530486928882693 998954875974466299165505)
                    ·
                      rfl

theorem cell23_5836373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_5836373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836373 prefixEnd_5836373 := by exact prefixLift 5836373
  have htrace : WordTrace (prefixWord ++ tailWord_5836373) baseStart_5836373 baseEnd_5836373 := by
    simpa [prefixWord, tailWord_5836373, baseEnd_5836373] using wordTrace_append hprefix tailTrace_5836373
  have hstable : (prefixWord ++ tailWord_5836373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836373).length < 2 ^ (prefixWord ++ tailWord_5836373).sum := by decide
  have hdescent : baseEnd_5836373 < baseStart_5836373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836376 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_5836376 : Nat := 118140960795 + 5836376 * 2 ^ 59
def prefixEnd_5836376 : Nat := 4983230072969 + 3 ^ 40 * 5836376 * 2
def baseEnd_5836376 : Nat := 2996866168365362385759001

theorem tailTrace_5836376 : CollatzResearch.WordTrace tailWord_5836376 prefixEnd_5836376 2996866168365362385759001 := by
  unfold tailWord_5836376
  simp only [CollatzResearch.WordTrace]
  refine ⟨106435060351907000254352491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141913413802542667005803321 106435060351907000254352491)
  ·
    refine ⟨159652590527860500381528737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106435060351907000254352491 159652590527860500381528737)
    ·
      refine ⟨119739442895895375286146553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159652590527860500381528737 119739442895895375286146553)
      ·
        refine ⟨89804582171921531464609915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119739442895895375286146553 89804582171921531464609915)
        ·
          refine ⟨134706873257882297196914873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89804582171921531464609915 134706873257882297196914873)
          ·
            refine ⟨101030154943411722897686155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134706873257882297196914873 101030154943411722897686155)
            ·
              refine ⟨151545232415117584346529233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101030154943411722897686155 151545232415117584346529233)
              ·
                refine ⟨113658924311338188259896925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151545232415117584346529233 113658924311338188259896925)
                ·
                  refine ⟨42622096616751820597461347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113658924311338188259896925 42622096616751820597461347)
                  ·
                    refine ⟨63933144925127730896192021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42622096616751820597461347 63933144925127730896192021)
                    ·
                      refine ⟨2996866168365362385759001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63933144925127730896192021 2996866168365362385759001)
                      ·
                        rfl

theorem cell23_5836376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_5836376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836376 prefixEnd_5836376 := by exact prefixLift 5836376
  have htrace : WordTrace (prefixWord ++ tailWord_5836376) baseStart_5836376 baseEnd_5836376 := by
    simpa [prefixWord, tailWord_5836376, baseEnd_5836376] using wordTrace_append hprefix tailTrace_5836376
  have hstable : (prefixWord ++ tailWord_5836376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836376).length < 2 ^ (prefixWord ++ tailWord_5836376).sum := by decide
  have hdescent : baseEnd_5836376 < baseStart_5836376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836396 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_5836396 : Nat := 118140960795 + 5836396 * 2 ^ 59
def prefixEnd_5836396 : Nat := 4983230072969 + 3 ^ 40 * 5836396 * 2
def baseEnd_5836396 : Nat := 2996876437978452307508909

theorem tailTrace_5836396 : CollatzResearch.WordTrace tailWord_5836396 prefixEnd_5836396 2996876437978452307508909 := by
  unfold tailWord_5836396
  simp only [CollatzResearch.WordTrace]
  refine ⟨106435425081870771962216521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141913900109161029282955361 106435425081870771962216521)
  ·
    refine ⟨79826568811403078971662391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106435425081870771962216521 79826568811403078971662391)
    ·
      refine ⟨119739853217104618457493587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79826568811403078971662391 119739853217104618457493587)
      ·
        refine ⟨179609779825656927686240381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119739853217104618457493587 179609779825656927686240381)
        ·
          refine ⟨67353667434621347882340143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179609779825656927686240381 67353667434621347882340143)
          ·
            refine ⟨101030501151932021823510215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67353667434621347882340143 101030501151932021823510215)
            ·
              refine ⟨151545751727898032735265323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101030501151932021823510215 151545751727898032735265323)
              ·
                refine ⟨227318627591847049102897985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151545751727898032735265323 227318627591847049102897985)
                ·
                  refine ⟨170488970693885286827173489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227318627591847049102897985 170488970693885286827173489)
                  ·
                    refine ⟨127866728020413965120380117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170488970693885286827173489 127866728020413965120380117)
                    ·
                      refine ⟨2996876437978452307508909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127866728020413965120380117 2996876437978452307508909)
                      ·
                        rfl

theorem cell23_5836396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_5836396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836396 prefixEnd_5836396 := by exact prefixLift 5836396
  have htrace : WordTrace (prefixWord ++ tailWord_5836396) baseStart_5836396 baseEnd_5836396 := by
    simpa [prefixWord, tailWord_5836396, baseEnd_5836396] using wordTrace_append hprefix tailTrace_5836396
  have hstable : (prefixWord ++ tailWord_5836396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836396).length < 2 ^ (prefixWord ++ tailWord_5836396).sum := by decide
  have hdescent : baseEnd_5836396 < baseStart_5836396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836417 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5836417 : Nat := 118140960795 + 5836417 * 2 ^ 59
def prefixEnd_5836417 : Nat := 4983230072969 + 3 ^ 40 * 5836417 * 2
def baseEnd_5836417 : Nat := 2996887221072196725346313

theorem tailTrace_5836417 : CollatzResearch.WordTrace tailWord_5836417 prefixEnd_5836417 2996887221072196725346313 := by
  unfold tailWord_5836417
  simp only [CollatzResearch.WordTrace]
  refine ⟨212871616096665464510947505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141914410731110309673965003 212871616096665464510947505)
  ·
    refine ⟨159653712072499098383210629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212871616096665464510947505 159653712072499098383210629)
    ·
      refine ⟨29935071013593580946851993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159653712072499098383210629 29935071013593580946851993)
      ·
        refine ⟨22451303260195185710138995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29935071013593580946851993 22451303260195185710138995)
        ·
          refine ⟨33676954890292778565208493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22451303260195185710138995 33676954890292778565208493)
          ·
            refine ⟨12628858083859791961953185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33676954890292778565208493 12628858083859791961953185)
            ·
              refine ⟨9471643562894843971464889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12628858083859791961953185 9471643562894843971464889)
              ·
                refine ⟨7103732672171132978598667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9471643562894843971464889 7103732672171132978598667)
                ·
                  refine ⟨10655599008256699467898001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103732672171132978598667 10655599008256699467898001)
                  ·
                    refine ⟨7991699256192524600923501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10655599008256699467898001 7991699256192524600923501)
                    ·
                      refine ⟨2996887221072196725346313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7991699256192524600923501 2996887221072196725346313)
                      ·
                        rfl

theorem cell23_5836417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5836417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836417 prefixEnd_5836417 := by exact prefixLift 5836417
  have htrace : WordTrace (prefixWord ++ tailWord_5836417) baseStart_5836417 baseEnd_5836417 := by
    simpa [prefixWord, tailWord_5836417, baseEnd_5836417] using wordTrace_append hprefix tailTrace_5836417
  have hstable : (prefixWord ++ tailWord_5836417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836417).length < 2 ^ (prefixWord ++ tailWord_5836417).sum := by decide
  have hdescent : baseEnd_5836417 < baseStart_5836417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836473 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5836473 : Nat := 118140960795 + 5836473 * 2 ^ 59
def prefixEnd_5836473 : Nat := 4983230072969 + 3 ^ 40 * 5836473 * 2
def baseEnd_5836473 : Nat := 2996915975988848506246055

theorem tailTrace_5836473 : CollatzResearch.WordTrace tailWord_5836473 prefixEnd_5836473 2996915975988848506246055 := by
  unfold tailWord_5836473
  simp only [CollatzResearch.WordTrace]
  refine ⟨212873658584462586074986073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141915772389641724049990715 212873658584462586074986073)
  ·
    refine ⟨159655243938346939556239555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212873658584462586074986073 159655243938346939556239555)
    ·
      refine ⟨239482865907520409334359333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159655243938346939556239555 239482865907520409334359333)
      ·
        refine ⟨44903037357660076750192375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239482865907520409334359333 44903037357660076750192375)
        ·
          refine ⟨67354556036490115125288563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44903037357660076750192375 67354556036490115125288563)
          ·
            refine ⟨101031834054735172687932845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67354556036490115125288563 101031834054735172687932845)
            ·
              refine ⟨37886937770525689757974817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101031834054735172687932845 37886937770525689757974817)
              ·
                refine ⟨28415203327894267318481113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37886937770525689757974817 28415203327894267318481113)
                ·
                  refine ⟨21311402495920700488860835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28415203327894267318481113 21311402495920700488860835)
                  ·
                    refine ⟨31967103743881050733291253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21311402495920700488860835 31967103743881050733291253)
                    ·
                      refine ⟨2996915975988848506246055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31967103743881050733291253 2996915975988848506246055)
                      ·
                        rfl

theorem cell23_5836473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5836473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836473 prefixEnd_5836473 := by exact prefixLift 5836473
  have htrace : WordTrace (prefixWord ++ tailWord_5836473) baseStart_5836473 baseEnd_5836473 := by
    simpa [prefixWord, tailWord_5836473, baseEnd_5836473] using wordTrace_append hprefix tailTrace_5836473
  have hstable : (prefixWord ++ tailWord_5836473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836473).length < 2 ^ (prefixWord ++ tailWord_5836473).sum := by decide
  have hdescent : baseEnd_5836473 < baseStart_5836473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836474 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_5836474 : Nat := 118140960795 + 5836474 * 2 ^ 59
def prefixEnd_5836474 : Nat := 4983230072969 + 3 ^ 40 * 5836474 * 2
def baseEnd_5836474 : Nat := 2996916489469503002333551

theorem tailTrace_5836474 : CollatzResearch.WordTrace tailWord_5836474 prefixEnd_5836474 2996916489469503002333551 := by
  unfold tailWord_5836474
  simp only [CollatzResearch.WordTrace]
  refine ⟨53218423764364740811443119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141915796704972642163848317 53218423764364740811443119)
  ·
    refine ⟨79827635646547111217164679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53218423764364740811443119 79827635646547111217164679)
    ·
      refine ⟨119741453469820666825747019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79827635646547111217164679 119741453469820666825747019)
      ·
        refine ⟨179612180204731000238620529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119741453469820666825747019 179612180204731000238620529)
        ·
          refine ⟨134709135153548250178965397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179612180204731000238620529 134709135153548250178965397)
          ·
            refine ⟨6314490710322574227139003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134709135153548250178965397 6314490710322574227139003)
            ·
              refine ⟨9471736065483861340708505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314490710322574227139003 9471736065483861340708505)
              ·
                refine ⟨7103802049112896005531379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9471736065483861340708505 7103802049112896005531379)
                ·
                  refine ⟨10655703073669344008297069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103802049112896005531379 10655703073669344008297069)
                  ·
                    refine ⟨3995888652626004003111401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10655703073669344008297069 3995888652626004003111401)
                    ·
                      refine ⟨2996916489469503002333551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995888652626004003111401 2996916489469503002333551)
                      ·
                        rfl

theorem cell23_5836474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_5836474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836474 prefixEnd_5836474 := by exact prefixLift 5836474
  have htrace : WordTrace (prefixWord ++ tailWord_5836474) baseStart_5836474 baseEnd_5836474 := by
    simpa [prefixWord, tailWord_5836474, baseEnd_5836474] using wordTrace_append hprefix tailTrace_5836474
  have hstable : (prefixWord ++ tailWord_5836474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836474).length < 2 ^ (prefixWord ++ tailWord_5836474).sum := by decide
  have hdescent : baseEnd_5836474 < baseStart_5836474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836504 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_5836504 : Nat := 118140960795 + 5836504 * 2 ^ 59
def prefixEnd_5836504 : Nat := 4983230072969 + 3 ^ 40 * 5836504 * 2
def baseEnd_5836504 : Nat := 2996931893889137884958413

theorem tailTrace_5836504 : CollatzResearch.WordTrace tailWord_5836504 prefixEnd_5836504 2996931893889137884958413 := by
  unfold tailWord_5836504
  simp only [CollatzResearch.WordTrace]
  refine ⟨106437394623675139184682283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141916526164900185579576377 106437394623675139184682283)
  ·
    refine ⟨159656091935512708777023425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106437394623675139184682283 159656091935512708777023425)
    ·
      refine ⟨119742068951634531582767569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159656091935512708777023425 119742068951634531582767569)
      ·
        refine ⟨89806551713725898687075677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119742068951634531582767569 89806551713725898687075677)
        ·
          refine ⟨33677456892647212007653379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89806551713725898687075677 33677456892647212007653379)
          ·
            refine ⟨50516185338970818011480069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33677456892647212007653379 50516185338970818011480069)
            ·
              refine ⟨9471784751057028377152513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50516185338970818011480069 9471784751057028377152513)
              ·
                refine ⟨7103838563292771282864385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9471784751057028377152513 7103838563292771282864385)
                ·
                  refine ⟨5327878922469578462148289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7103838563292771282864385 5327878922469578462148289)
                  ·
                    refine ⟨3995909191852183846611217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5327878922469578462148289 3995909191852183846611217)
                    ·
                      refine ⟨2996931893889137884958413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995909191852183846611217 2996931893889137884958413)
                      ·
                        rfl

theorem cell23_5836504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_5836504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836504 prefixEnd_5836504 := by exact prefixLift 5836504
  have htrace : WordTrace (prefixWord ++ tailWord_5836504) baseStart_5836504 baseEnd_5836504 := by
    simpa [prefixWord, tailWord_5836504, baseEnd_5836504] using wordTrace_append hprefix tailTrace_5836504
  have hstable : (prefixWord ++ tailWord_5836504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836504).length < 2 ^ (prefixWord ++ tailWord_5836504).sum := by decide
  have hdescent : baseEnd_5836504 < baseStart_5836504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836520 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5836520 : Nat := 118140960795 + 5836520 * 2 ^ 59
def prefixEnd_5836520 : Nat := 4983230072969 + 3 ^ 40 * 5836520 * 2
def baseEnd_5836520 : Nat := 2996940109579609822358339

theorem tailTrace_5836520 : CollatzResearch.WordTrace tailWord_5836520 prefixEnd_5836520 2996940109579609822358339 := by
  unfold tailWord_5836520
  simp only [CollatzResearch.WordTrace]
  refine ⟨106437686407646156550973507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141916915210194875401298009 106437686407646156550973507)
  ·
    refine ⟨159656529611469234826460261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106437686407646156550973507 159656529611469234826460261)
    ·
      refine ⟨29935599302150481529961299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159656529611469234826460261 29935599302150481529961299)
      ·
        refine ⟨44903398953225722294941949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29935599302150481529961299 44903398953225722294941949)
        ·
          refine ⟨16838774607459645860603231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44903398953225722294941949 16838774607459645860603231)
          ·
            refine ⟨25258161911189468790904847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16838774607459645860603231 25258161911189468790904847)
            ·
              refine ⟨37887242866784203186357271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25258161911189468790904847 37887242866784203186357271)
              ·
                refine ⟨56830864300176304779535907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37887242866784203186357271 56830864300176304779535907)
                ·
                  refine ⟨85246296450264457169303861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56830864300176304779535907 85246296450264457169303861)
                  ·
                    refine ⟨7991840292212292859622237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85246296450264457169303861 7991840292212292859622237)
                    ·
                      refine ⟨2996940109579609822358339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7991840292212292859622237 2996940109579609822358339)
                      ·
                        rfl

theorem cell23_5836520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5836520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836520 prefixEnd_5836520 := by exact prefixLift 5836520
  have htrace : WordTrace (prefixWord ++ tailWord_5836520) baseStart_5836520 baseEnd_5836520 := by
    simpa [prefixWord, tailWord_5836520, baseEnd_5836520] using wordTrace_append hprefix tailTrace_5836520
  have hstable : (prefixWord ++ tailWord_5836520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836520).length < 2 ^ (prefixWord ++ tailWord_5836520).sum := by decide
  have hdescent : baseEnd_5836520 < baseStart_5836520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836523 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 4, 5]
def baseStart_5836523 : Nat := 118140960795 + 5836523 * 2 ^ 59
def prefixEnd_5836523 : Nat := 4983230072969 + 3 ^ 40 * 5836523 * 2
def baseEnd_5836523 : Nat := 998980550007191103540275

theorem tailTrace_5836523 : CollatzResearch.WordTrace tailWord_5836523 prefixEnd_5836523 998980550007191103540275 := by
  unfold tailWord_5836523
  simp only [CollatzResearch.WordTrace]
  refine ⟨212875482234281444614306223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141916988156187629742870815 212875482234281444614306223)
  ·
    refine ⟨319313223351422166921459335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212875482234281444614306223 319313223351422166921459335)
    ·
      refine ⟨478969835027133250382189003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319313223351422166921459335 478969835027133250382189003)
      ·
        refine ⟨718454752540699875573283505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478969835027133250382189003 718454752540699875573283505)
        ·
          refine ⟨538841064405524906679962629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718454752540699875573283505 538841064405524906679962629)
          ·
            refine ⟨101032699576035920002492993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 538841064405524906679962629 101032699576035920002492993)
            ·
              refine ⟨75774524682026940001869745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101032699576035920002492993 75774524682026940001869745)
              ·
                refine ⟨56830893511520205001402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75774524682026940001869745 56830893511520205001402309)
                ·
                  refine ⟨10655792533410038437762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56830893511520205001402309 10655792533410038437762933)
                  ·
                    refine ⟨998980550007191103540275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10655792533410038437762933 998980550007191103540275)
                    ·
                      rfl

theorem cell23_5836523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 5].length) (baseStart_5836523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836523 prefixEnd_5836523 := by exact prefixLift 5836523
  have htrace : WordTrace (prefixWord ++ tailWord_5836523) baseStart_5836523 baseEnd_5836523 := by
    simpa [prefixWord, tailWord_5836523, baseEnd_5836523] using wordTrace_append hprefix tailTrace_5836523
  have hstable : (prefixWord ++ tailWord_5836523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836523).length < 2 ^ (prefixWord ++ tailWord_5836523).sum := by decide
  have hdescent : baseEnd_5836523 < baseStart_5836523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836577 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5836577 : Nat := 118140960795 + 5836577 * 2 ^ 59
def prefixEnd_5836577 : Nat := 4983230072969 + 3 ^ 40 * 5836577 * 2
def baseEnd_5836577 : Nat := 2996969377976916099345577

theorem tailTrace_5836577 : CollatzResearch.WordTrace tailWord_5836577 prefixEnd_5836577 2996969377976916099345577 := by
  unfold tailWord_5836577
  simp only [CollatzResearch.WordTrace]
  refine ⟨212877451776085811836771985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141918301184057207891181323 212877451776085811836771985)
  ·
    refine ⟨159658088832064358877578989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212877451776085811836771985 159658088832064358877578989)
    ·
      refine ⟨59871783312024134579092121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159658088832064358877578989 59871783312024134579092121)
      ·
        refine ⟨44903837484018100934319091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59871783312024134579092121 44903837484018100934319091)
        ·
          refine ⟨67355756226027151401478637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44903837484018100934319091 67355756226027151401478637)
          ·
            refine ⟨25258408584760181775554489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67355756226027151401478637 25258408584760181775554489)
            ·
              refine ⟨18943806438570136331665867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25258408584760181775554489 18943806438570136331665867)
              ·
                refine ⟨28415709657855204497498801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18943806438570136331665867 28415709657855204497498801)
                ·
                  refine ⟨21311782243391403373124101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28415709657855204497498801 21311782243391403373124101)
                  ·
                    refine ⟨3995959170635888132460769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21311782243391403373124101 3995959170635888132460769)
                    ·
                      refine ⟨2996969377976916099345577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3995959170635888132460769 2996969377976916099345577)
                      ·
                        rfl

theorem cell23_5836577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5836577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836577 prefixEnd_5836577 := by exact prefixLift 5836577
  have htrace : WordTrace (prefixWord ++ tailWord_5836577) baseStart_5836577 baseEnd_5836577 := by
    simpa [prefixWord, tailWord_5836577, baseEnd_5836577] using wordTrace_append hprefix tailTrace_5836577
  have hstable : (prefixWord ++ tailWord_5836577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836577).length < 2 ^ (prefixWord ++ tailWord_5836577).sum := by decide
  have hdescent : baseEnd_5836577 < baseStart_5836577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836604 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_5836604 : Nat := 118140960795 + 5836604 * 2 ^ 59
def prefixEnd_5836604 : Nat := 4983230072969 + 3 ^ 40 * 5836604 * 2
def baseEnd_5836604 : Nat := 998994413984862497902651

theorem tailTrace_5836604 : CollatzResearch.WordTrace tailWord_5836604 prefixEnd_5836604 998994413984862497902651 := by
  unfold tailWord_5836604
  simp only [CollatzResearch.WordTrace]
  refine ⟨106439218273493997724002433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141918957697991996965336577 106439218273493997724002433)
  ·
    refine ⟨79829413705120498293001825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106439218273493997724002433 79829413705120498293001825)
    ·
      refine ⟨59872060278840373719751369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79829413705120498293001825 59872060278840373719751369)
      ·
        refine ⟨44904045209130280289813527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59872060278840373719751369 44904045209130280289813527)
        ·
          refine ⟨67356067813695420434720291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44904045209130280289813527 67356067813695420434720291)
          ·
            refine ⟨101034101720543130652080437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67356067813695420434720291 101034101720543130652080437)
            ·
              refine ⟨9471947036300918498632541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101034101720543130652080437 9471947036300918498632541)
              ·
                refine ⟨3551980138612844436987203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9471947036300918498632541 3551980138612844436987203)
                ·
                  refine ⟨5327970207919266655480805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551980138612844436987203 5327970207919266655480805)
                  ·
                    refine ⟨998994413984862497902651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327970207919266655480805 998994413984862497902651)
                    ·
                      rfl

theorem cell23_5836604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_5836604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836604 prefixEnd_5836604 := by exact prefixLift 5836604
  have htrace : WordTrace (prefixWord ++ tailWord_5836604) baseStart_5836604 baseEnd_5836604 := by
    simpa [prefixWord, tailWord_5836604, baseEnd_5836604] using wordTrace_append hprefix tailTrace_5836604
  have hstable : (prefixWord ++ tailWord_5836604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836604).length < 2 ^ (prefixWord ++ tailWord_5836604).sum := by decide
  have hdescent : baseEnd_5836604 < baseStart_5836604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836621 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_5836621 : Nat := 118140960795 + 5836621 * 2 ^ 59
def prefixEnd_5836621 : Nat := 4983230072969 + 3 ^ 40 * 5836621 * 2
def baseEnd_5836621 : Nat := 998997323708571309065125

theorem tailTrace_5836621 : CollatzResearch.WordTrace tailWord_5836621 prefixEnd_5836621 998997323708571309065125 := by
  unfold tailWord_5836621
  simp only [CollatzResearch.WordTrace]
  refine ⟨212879056587926407351373717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141919371058617604900915811 212879056587926407351373717)
  ·
    refine ⟨9978705777559050344595643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212879056587926407351373717 9978705777559050344595643)
    ·
      refine ⟨14968058666338575516893465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9978705777559050344595643 14968058666338575516893465)
      ·
        refine ⟨11226043999753931637670099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14968058666338575516893465 11226043999753931637670099)
        ·
          refine ⟨16839065999630897456505149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226043999753931637670099 16839065999630897456505149)
          ·
            refine ⟨6314649749861586546189431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16839065999630897456505149 6314649749861586546189431)
            ·
              refine ⟨9471974624792379819284147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314649749861586546189431 9471974624792379819284147)
              ·
                refine ⟨14207961937188569728926221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9471974624792379819284147 14207961937188569728926221)
                ·
                  refine ⟨5327985726445713648347333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14207961937188569728926221 5327985726445713648347333)
                  ·
                    refine ⟨998997323708571309065125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327985726445713648347333 998997323708571309065125)
                    ·
                      rfl

theorem cell23_5836621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_5836621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836621 prefixEnd_5836621 := by exact prefixLift 5836621
  have htrace : WordTrace (prefixWord ++ tailWord_5836621) baseStart_5836621 baseEnd_5836621 := by
    simpa [prefixWord, tailWord_5836621, baseEnd_5836621] using wordTrace_append hprefix tailTrace_5836621
  have hstable : (prefixWord ++ tailWord_5836621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836621).length < 2 ^ (prefixWord ++ tailWord_5836621).sum := by decide
  have hdescent : baseEnd_5836621 < baseStart_5836621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836661 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5836661 : Nat := 118140960795 + 5836661 * 2 ^ 59
def prefixEnd_5836661 : Nat := 4983230072969 + 3 ^ 40 * 5836661 * 2
def baseEnd_5836661 : Nat := 2997012510351893770695191

theorem tailTrace_5836661 : CollatzResearch.WordTrace tailWord_5836661 prefixEnd_5836661 2997012510351893770695191 := by
  unfold tailWord_5836661
  simp only [CollatzResearch.WordTrace]
  refine ⟨212880515507781494182829837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141920343671854329455219891 212880515507781494182829837)
  ·
    refine ⟨79830193315418060318561189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212880515507781494182829837 79830193315418060318561189)
    ·
      refine ⟨14968161246640886309730223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79830193315418060318561189 14968161246640886309730223)
      ·
        refine ⟨22452241869961329464595335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14968161246640886309730223 22452241869961329464595335)
        ·
          refine ⟨33678362804941994196893003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22452241869961329464595335 33678362804941994196893003)
          ·
            refine ⟨50517544207412991295339505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33678362804941994196893003 50517544207412991295339505)
            ·
              refine ⟨37888158155559743471504629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50517544207412991295339505 37888158155559743471504629)
              ·
                refine ⟨3552014827083725950453559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37888158155559743471504629 3552014827083725950453559)
                ·
                  refine ⟨5328022240625588925680339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552014827083725950453559 5328022240625588925680339)
                  ·
                    refine ⟨7992033360938383388520509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328022240625588925680339 7992033360938383388520509)
                    ·
                      refine ⟨2997012510351893770695191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992033360938383388520509 2997012510351893770695191)
                      ·
                        rfl

theorem cell23_5836661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5836661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836661 prefixEnd_5836661 := by exact prefixLift 5836661
  have htrace : WordTrace (prefixWord ++ tailWord_5836661) baseStart_5836661 baseEnd_5836661 := by
    simpa [prefixWord, tailWord_5836661, baseEnd_5836661] using wordTrace_append hprefix tailTrace_5836661
  have hstable : (prefixWord ++ tailWord_5836661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836661).length < 2 ^ (prefixWord ++ tailWord_5836661).sum := by decide
  have hdescent : baseEnd_5836661 < baseStart_5836661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836684 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_5836684 : Nat := 118140960795 + 5836684 * 2 ^ 59
def prefixEnd_5836684 : Nat := 4983230072969 + 3 ^ 40 * 5836684 * 2
def baseEnd_5836684 : Nat := 2997024320406947180707585

theorem tailTrace_5836684 : CollatzResearch.WordTrace tailWord_5836684 prefixEnd_5836684 2997024320406947180707585 := by
  unfold tailWord_5836684
  simp only [CollatzResearch.WordTrace]
  refine ⟨106440677193349084555458553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141920902924465446073944737 106440677193349084555458553)
  ·
    refine ⟨79830507895011813416593915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106440677193349084555458553 79830507895011813416593915)
    ·
      refine ⟨119745761842517720124890873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79830507895011813416593915 119745761842517720124890873)
      ·
        refine ⟨89809321381888290093668155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119745761842517720124890873 89809321381888290093668155)
        ·
          refine ⟨134713982072832435140502233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89809321381888290093668155 134713982072832435140502233)
          ·
            refine ⟨101035486554624326355376675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134713982072832435140502233 101035486554624326355376675)
            ·
              refine ⟨151553229831936489533065013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101035486554624326355376675 151553229831936489533065013)
              ·
                refine ⟨14208115296744045893724845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151553229831936489533065013 14208115296744045893724845)
                ·
                  refine ⟨5328043236279017210146817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14208115296744045893724845 5328043236279017210146817)
                  ·
                    refine ⟨3996032427209262907610113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5328043236279017210146817 3996032427209262907610113)
                    ·
                      refine ⟨2997024320406947180707585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996032427209262907610113 2997024320406947180707585)
                      ·
                        rfl

theorem cell23_5836684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_5836684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836684 prefixEnd_5836684 := by exact prefixLift 5836684
  have htrace : WordTrace (prefixWord ++ tailWord_5836684) baseStart_5836684 baseEnd_5836684 := by
    simpa [prefixWord, tailWord_5836684, baseEnd_5836684] using wordTrace_append hprefix tailTrace_5836684
  have hstable : (prefixWord ++ tailWord_5836684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836684).length < 2 ^ (prefixWord ++ tailWord_5836684).sum := by decide
  have hdescent : baseEnd_5836684 < baseStart_5836684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836701 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_5836701 : Nat := 118140960795 + 5836701 * 2 ^ 59
def prefixEnd_5836701 : Nat := 4983230072969 + 3 ^ 40 * 5836701 * 2
def baseEnd_5836701 : Nat := 2997033049578073614195007

theorem tailTrace_5836701 : CollatzResearch.WordTrace tailWord_5836701 prefixEnd_5836701 2997033049578073614195007 := by
  unfold tailWord_5836701
  simp only [CollatzResearch.WordTrace]
  refine ⟨212881974427636581014285957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141921316285091054009523971 212881974427636581014285957)
  ·
    refine ⟨39915370205181858940178617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212881974427636581014285957 39915370205181858940178617)
    ·
      refine ⟨29936527653886394205133963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39915370205181858940178617 29936527653886394205133963)
      ·
        refine ⟨44904791480829591307700945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29936527653886394205133963 44904791480829591307700945)
        ·
          refine ⟨33678593610622193480775709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44904791480829591307700945 33678593610622193480775709)
          ·
            refine ⟨12629472603983322555290891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33678593610622193480775709 12629472603983322555290891)
            ·
              refine ⟨18944208905974983832936337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12629472603983322555290891 18944208905974983832936337)
              ·
                refine ⟨14208156679481237874702253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18944208905974983832936337 14208156679481237874702253)
                ·
                  refine ⟨5328058754805464203013345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14208156679481237874702253 5328058754805464203013345)
                  ·
                    refine ⟨3996044066104098152260009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5328058754805464203013345 3996044066104098152260009)
                    ·
                      refine ⟨2997033049578073614195007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996044066104098152260009 2997033049578073614195007)
                      ·
                        rfl

theorem cell23_5836701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_5836701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836701 prefixEnd_5836701 := by exact prefixLift 5836701
  have htrace : WordTrace (prefixWord ++ tailWord_5836701) baseStart_5836701 baseEnd_5836701 := by
    simpa [prefixWord, tailWord_5836701, baseEnd_5836701] using wordTrace_append hprefix tailTrace_5836701
  have hstable : (prefixWord ++ tailWord_5836701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836701).length < 2 ^ (prefixWord ++ tailWord_5836701).sum := by decide
  have hdescent : baseEnd_5836701 < baseStart_5836701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836721 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_5836721 : Nat := 118140960795 + 5836721 * 2 ^ 59
def prefixEnd_5836721 : Nat := 4983230072969 + 3 ^ 40 * 5836721 * 2
def baseEnd_5836721 : Nat := 2997043319191163535944915

theorem tailTrace_5836721 : CollatzResearch.WordTrace tailWord_5836721 prefixEnd_5836721 2997043319191163535944915 := by
  unfold tailWord_5836721
  simp only [CollatzResearch.WordTrace]
  refine ⟨212882703887564124430014017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141921802591709416286676011 212882703887564124430014017)
  ·
    refine ⟨159662027915673093322510513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212882703887564124430014017 159662027915673093322510513)
    ·
      refine ⟨119746520936754819991882885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159662027915673093322510513 119746520936754819991882885)
      ·
        refine ⟨22452472675641528748478041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119746520936754819991882885 22452472675641528748478041)
        ·
          refine ⟨16839354506731146561358531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22452472675641528748478041 16839354506731146561358531)
          ·
            refine ⟨25259031760096719842037797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16839354506731146561358531 25259031760096719842037797)
            ·
              refine ⟨4736068455018134970382087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25259031760096719842037797 4736068455018134970382087)
              ·
                refine ⟨7104102682527202455573131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736068455018134970382087 7104102682527202455573131)
                ·
                  refine ⟨10656154023790803683359697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104102682527202455573131 10656154023790803683359697)
                  ·
                    refine ⟨7992115517843102762519773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10656154023790803683359697 7992115517843102762519773)
                    ·
                      refine ⟨2997043319191163535944915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992115517843102762519773 2997043319191163535944915)
                      ·
                        rfl

theorem cell23_5836721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_5836721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836721 prefixEnd_5836721 := by exact prefixLift 5836721
  have htrace : WordTrace (prefixWord ++ tailWord_5836721) baseStart_5836721 baseEnd_5836721 := by
    simpa [prefixWord, tailWord_5836721, baseEnd_5836721] using wordTrace_append hprefix tailTrace_5836721
  have hstable : (prefixWord ++ tailWord_5836721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836721).length < 2 ^ (prefixWord ++ tailWord_5836721).sum := by decide
  have hdescent : baseEnd_5836721 < baseStart_5836721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836724 : List Nat := [2, 5, 2, 1, 2, 1, 10]
def baseStart_5836724 : Nat := 118140960795 + 5836724 * 2 ^ 59
def prefixEnd_5836724 : Nat := 4983230072969 + 3 ^ 40 * 5836724 * 2
def baseEnd_5836724 : Nat := 37000553822631197829721

theorem tailTrace_5836724 : CollatzResearch.WordTrace tailWord_5836724 prefixEnd_5836724 37000553822631197829721 := by
  unfold tailWord_5836724
  simp only [CollatzResearch.WordTrace]
  refine ⟨106441406653276627971186613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141921875537702170628248817 106441406653276627971186613)
  ·
    refine ⟨9978881873744683872298745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106441406653276627971186613 9978881873744683872298745)
    ·
      refine ⟨7484161405308512904224059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9978881873744683872298745 7484161405308512904224059)
      ·
        refine ⟨11226242107962769356336089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7484161405308512904224059 11226242107962769356336089)
        ·
          refine ⟨8419681580972077017252067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11226242107962769356336089 8419681580972077017252067)
          ·
            refine ⟨12629522371458115525878101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8419681580972077017252067 12629522371458115525878101)
            ·
              refine ⟨37000553822631197829721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12629522371458115525878101 37000553822631197829721)
              ·
                rfl

theorem cell23_5836724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 10].length) (baseStart_5836724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836724 prefixEnd_5836724 := by exact prefixLift 5836724
  have htrace : WordTrace (prefixWord ++ tailWord_5836724) baseStart_5836724 baseEnd_5836724 := by
    simpa [prefixWord, tailWord_5836724, baseEnd_5836724] using wordTrace_append hprefix tailTrace_5836724
  have hstable : (prefixWord ++ tailWord_5836724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836724).length < 2 ^ (prefixWord ++ tailWord_5836724).sum := by decide
  have hdescent : baseEnd_5836724 < baseStart_5836724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836730 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_5836730 : Nat := 118140960795 + 5836730 * 2 ^ 59
def prefixEnd_5836730 : Nat := 4983230072969 + 3 ^ 40 * 5836730 * 2
def baseEnd_5836730 : Nat := 2997047940517054000732373

theorem tailTrace_5836730 : CollatzResearch.WordTrace tailWord_5836730 prefixEnd_5836730 2997047940517054000732373 := by
  unfold tailWord_5836730
  simp only [CollatzResearch.WordTrace]
  refine ⟨53220758036132879741772911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141922021429687679311394429 53220758036132879741772911)
  ·
    refine ⟨79831137054199319612659367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53220758036132879741772911 79831137054199319612659367)
    ·
      refine ⟨119746705581298979418989051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79831137054199319612659367 119746705581298979418989051)
      ·
        refine ⟨179620058371948469128483577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119746705581298979418989051 179620058371948469128483577)
        ·
          refine ⟨134715043778961351846362683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179620058371948469128483577 134715043778961351846362683)
          ·
            refine ⟨202072565668442027769544025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134715043778961351846362683 202072565668442027769544025)
            ·
              refine ⟨151554424251331520827158019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202072565668442027769544025 151554424251331520827158019)
              ·
                refine ⟨227331636376997281240737029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151554424251331520827158019 227331636376997281240737029)
                ·
                  refine ⟨42624681820686990232638193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227331636376997281240737029 42624681820686990232638193)
                  ·
                    refine ⟨31968511365515242674478645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42624681820686990232638193 31968511365515242674478645)
                    ·
                      refine ⟨2997047940517054000732373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31968511365515242674478645 2997047940517054000732373)
                      ·
                        rfl

theorem cell23_5836730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_5836730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836730 prefixEnd_5836730 := by exact prefixLift 5836730
  have htrace : WordTrace (prefixWord ++ tailWord_5836730) baseStart_5836730 baseEnd_5836730 := by
    simpa [prefixWord, tailWord_5836730, baseEnd_5836730] using wordTrace_append hprefix tailTrace_5836730
  have hstable : (prefixWord ++ tailWord_5836730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836730).length < 2 ^ (prefixWord ++ tailWord_5836730).sum := by decide
  have hdescent : baseEnd_5836730 < baseStart_5836730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836751 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 2, 1, 3]
def baseStart_5836751 : Nat := 118140960795 + 5836751 * 2 ^ 59
def prefixEnd_5836751 : Nat := 4983230072969 + 3 ^ 40 * 5836751 * 2
def baseEnd_5836751 : Nat := 2997058723610798418569777

theorem tailTrace_5836751 : CollatzResearch.WordTrace tailWord_5836751 prefixEnd_5836751 2997058723610798418569777 := by
  unfold tailWord_5836751
  simp only [CollatzResearch.WordTrace]
  refine ⟨212883798077455439553606107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141922532051636959702404071 212883798077455439553606107)
  ·
    refine ⟨319325697116183159330409161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212883798077455439553606107 319325697116183159330409161)
    ·
      refine ⟨239494272837137369497806871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319325697116183159330409161 239494272837137369497806871)
      ·
        refine ⟨359241409255706054246710307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239494272837137369497806871 359241409255706054246710307)
        ·
          refine ⟨538862113883559081370065461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359241409255706054246710307 538862113883559081370065461)
          ·
            refine ⟨50518323176583663878443637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 538862113883559081370065461 50518323176583663878443637)
            ·
              refine ⟨4736092797804718488604091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50518323176583663878443637 4736092797804718488604091)
              ·
                refine ⟨7104139196707077732906137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736092797804718488604091 7104139196707077732906137)
                ·
                  refine ⟨5328104397530308299679603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7104139196707077732906137 5328104397530308299679603)
                  ·
                    refine ⟨7992156596295462449519405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328104397530308299679603 7992156596295462449519405)
                    ·
                      refine ⟨2997058723610798418569777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992156596295462449519405 2997058723610798418569777)
                      ·
                        rfl

theorem cell23_5836751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 1, 3].length) (baseStart_5836751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836751 prefixEnd_5836751 := by exact prefixLift 5836751
  have htrace : WordTrace (prefixWord ++ tailWord_5836751) baseStart_5836751 baseEnd_5836751 := by
    simpa [prefixWord, tailWord_5836751, baseEnd_5836751] using wordTrace_append hprefix tailTrace_5836751
  have hstable : (prefixWord ++ tailWord_5836751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836751).length < 2 ^ (prefixWord ++ tailWord_5836751).sum := by decide
  have hdescent : baseEnd_5836751 < baseStart_5836751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836758 : List Nat := [5, 2, 1, 1, 4, 1, 2, 7]
def baseStart_5836758 : Nat := 118140960795 + 5836758 * 2 ^ 59
def prefixEnd_5836758 : Nat := 4983230072969 + 3 ^ 40 * 5836758 * 2
def baseEnd_5836758 : Nat := 111002308073162218191935

theorem tailTrace_5836758 : CollatzResearch.WordTrace tailWord_5836758 prefixEnd_5836758 111002308073162218191935 := by
  unfold tailWord_5836758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13305253336776879984319433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141922702258953386499407285 13305253336776879984319433)
  ·
    refine ⟨9978940002582659988239575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13305253336776879984319433 9978940002582659988239575)
    ·
      refine ⟨14968410003873989982359363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9978940002582659988239575 14968410003873989982359363)
      ·
        refine ⟨22452615005810984973539045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14968410003873989982359363 22452615005810984973539045)
        ·
          refine ⟨4209865313589559682538571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22452615005810984973539045 4209865313589559682538571)
          ·
            refine ⟨6314797970384339523807857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209865313589559682538571 6314797970384339523807857)
            ·
              refine ⟨4736098477788254642855893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6314797970384339523807857 4736098477788254642855893)
              ·
                refine ⟨111002308073162218191935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4736098477788254642855893 111002308073162218191935)
                ·
                  rfl

theorem cell23_5836758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_5836758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836758 prefixEnd_5836758 := by exact prefixLift 5836758
  have htrace : WordTrace (prefixWord ++ tailWord_5836758) baseStart_5836758 baseEnd_5836758 := by
    simpa [prefixWord, tailWord_5836758, baseEnd_5836758] using wordTrace_append hprefix tailTrace_5836758
  have hstable : (prefixWord ++ tailWord_5836758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836758).length < 2 ^ (prefixWord ++ tailWord_5836758).sum := by decide
  have hdescent : baseEnd_5836758 < baseStart_5836758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836780 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 9]
def baseStart_5836780 : Nat := 118140960795 + 5836780 * 2 ^ 59
def prefixEnd_5836780 : Nat := 4983230072969 + 3 ^ 40 * 5836780 * 2
def baseEnd_5836780 : Nat := 333008179394419867234127

theorem tailTrace_5836780 : CollatzResearch.WordTrace tailWord_5836780 prefixEnd_5836780 333008179394419867234127 := by
  unfold tailWord_5836780
  simp only [CollatzResearch.WordTrace]
  refine ⟨106442427897175188753205897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141923237196233585004274529 106442427897175188753205897)
  ·
    refine ⟨79831820922881391564904423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106442427897175188753205897 79831820922881391564904423)
    ·
      refine ⟨119747731384322087347356635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79831820922881391564904423 119747731384322087347356635)
      ·
        refine ⟨179621597076483131021034953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119747731384322087347356635 179621597076483131021034953)
        ·
          refine ⟨134716197807362348265776215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179621597076483131021034953 134716197807362348265776215)
          ·
            refine ⟨202074296711043522398664323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134716197807362348265776215 202074296711043522398664323)
            ·
              refine ⟨303111445066565283597996485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202074296711043522398664323 303111445066565283597996485)
              ·
                refine ⟨56833395949980990674624341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303111445066565283597996485 56833395949980990674624341)
                ·
                  refine ⟨333008179394419867234127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56833395949980990674624341 333008179394419867234127)
                  ·
                    rfl

theorem cell23_5836780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_5836780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836780 prefixEnd_5836780 := by exact prefixLift 5836780
  have htrace : WordTrace (prefixWord ++ tailWord_5836780) baseStart_5836780 baseEnd_5836780 := by
    simpa [prefixWord, tailWord_5836780, baseEnd_5836780] using wordTrace_append hprefix tailTrace_5836780
  have hstable : (prefixWord ++ tailWord_5836780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836780).length < 2 ^ (prefixWord ++ tailWord_5836780).sum := by decide
  have hdescent : baseEnd_5836780 < baseStart_5836780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836797 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 7]
def baseStart_5836797 : Nat := 118140960795 + 5836797 * 2 ^ 59
def prefixEnd_5836797 : Nat := 4983230072969 + 3 ^ 40 * 5836797 * 2
def baseEnd_5836797 : Nat := 333009149302322804288285

theorem tailTrace_5836797 : CollatzResearch.WordTrace tailWord_5836797 prefixEnd_5836797 333009149302322804288285 := by
  unfold tailWord_5836797
  simp only [CollatzResearch.WordTrace]
  refine ⟨212885475835288789409780645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141923650556859192939853763 212885475835288789409780645)
  ·
    refine ⟨39916026719116648014333871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212885475835288789409780645 39916026719116648014333871)
    ·
      refine ⟨59874040078674972021500807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39916026719116648014333871 59874040078674972021500807)
      ·
        refine ⟨89811060118012458032251211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59874040078674972021500807 89811060118012458032251211)
        ·
          refine ⟨134716590177018687048376817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89811060118012458032251211 134716590177018687048376817)
          ·
            refine ⟨101037442632764015286282613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134716590177018687048376817 101037442632764015286282613)
            ·
              refine ⟨9472260246821626433088995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101037442632764015286282613 9472260246821626433088995)
              ·
                refine ⟨14208390370232439649633493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9472260246821626433088995 14208390370232439649633493)
                ·
                  refine ⟨333009149302322804288285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14208390370232439649633493 333009149302322804288285)
                  ·
                    rfl

theorem cell23_5836797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_5836797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836797 prefixEnd_5836797 := by exact prefixLift 5836797
  have htrace : WordTrace (prefixWord ++ tailWord_5836797) baseStart_5836797 baseEnd_5836797 := by
    simpa [prefixWord, tailWord_5836797, baseEnd_5836797] using wordTrace_append hprefix tailTrace_5836797
  have hstable : (prefixWord ++ tailWord_5836797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836797).length < 2 ^ (prefixWord ++ tailWord_5836797).sum := by decide
  have hdescent : baseEnd_5836797 < baseStart_5836797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_5836800 : Nat := 118140960795 + 5836800 * 2 ^ 59
def prefixEnd_5836800 : Nat := 4983230072969 + 3 ^ 40 * 5836800 * 2
def baseEnd_5836800 : Nat := 2997083884162868726857051

theorem tailTrace_5836800 : CollatzResearch.WordTrace tailWord_5836800 prefixEnd_5836800 2997083884162868726857051 := by
  unfold tailWord_5836800
  simp only [CollatzResearch.WordTrace]
  refine ⟨106442792627138960461069927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141923723502851947281426569 106442792627138960461069927)
  ·
    refine ⟨159664188940708440691604891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106442792627138960461069927 159664188940708440691604891)
    ·
      refine ⟨239496283411062661037407337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159664188940708440691604891 239496283411062661037407337)
      ·
        refine ⟨179622212558296995778055503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239496283411062661037407337 179622212558296995778055503)
        ·
          refine ⟨269433318837445493667083255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179622212558296995778055503 269433318837445493667083255)
          ·
            refine ⟨404149978256168240500624883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269433318837445493667083255 404149978256168240500624883)
            ·
              refine ⟨606224967384252360750937325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404149978256168240500624883 606224967384252360750937325)
              ·
                refine ⟨227334362769094635281601497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 606224967384252360750937325 227334362769094635281601497)
                ·
                  refine ⟨170500772076820976461201123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227334362769094635281601497 170500772076820976461201123)
                  ·
                    refine ⟨255751158115231464691801685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170500772076820976461201123 255751158115231464691801685)
                    ·
                      refine ⟨2997083884162868726857051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255751158115231464691801685 2997083884162868726857051)
                      ·
                        rfl

theorem cell23_5836800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_5836800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836800 prefixEnd_5836800 := by exact prefixLift 5836800
  have htrace : WordTrace (prefixWord ++ tailWord_5836800) baseStart_5836800 baseEnd_5836800 := by
    simpa [prefixWord, tailWord_5836800, baseEnd_5836800] using wordTrace_append hprefix tailTrace_5836800
  have hstable : (prefixWord ++ tailWord_5836800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836800).length < 2 ^ (prefixWord ++ tailWord_5836800).sum := by decide
  have hdescent : baseEnd_5836800 < baseStart_5836800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836837 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_5836837 : Nat := 118140960795 + 5836837 * 2 ^ 59
def prefixEnd_5836837 : Nat := 4983230072969 + 3 ^ 40 * 5836837 * 2
def baseEnd_5836837 : Nat := 2997102882947085082094381

theorem tailTrace_5836837 : CollatzResearch.WordTrace tailWord_5836837 prefixEnd_5836837 2997102882947085082094381 := by
  unfold tailWord_5836837
  simp only [CollatzResearch.WordTrace]
  refine ⟨212886934755143876241236765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141924623170095917494157843 212886934755143876241236765)
  ·
    refine ⟨79832600533178953590463787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212886934755143876241236765 79832600533178953590463787)
    ·
      refine ⟨119748900799768430385695681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79832600533178953590463787 119748900799768430385695681)
      ·
        refine ⟨89811675599826322789271761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119748900799768430385695681 89811675599826322789271761)
        ·
          refine ⟨67358756699869742091953821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89811675599826322789271761 67358756699869742091953821)
          ·
            refine ⟨25259533762451153284482683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67358756699869742091953821 25259533762451153284482683)
            ·
              refine ⟨37889300643676729926724025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25259533762451153284482683 37889300643676729926724025)
              ·
                refine ⟨28416975482757547445043019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37889300643676729926724025 28416975482757547445043019)
                ·
                  refine ⟨42625463224136321167564529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28416975482757547445043019 42625463224136321167564529)
                  ·
                    refine ⟨31969097418102240875673397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42625463224136321167564529 31969097418102240875673397)
                    ·
                      refine ⟨2997102882947085082094381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31969097418102240875673397 2997102882947085082094381)
                      ·
                        rfl

theorem cell23_5836837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_5836837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836837 prefixEnd_5836837 := by exact prefixLift 5836837
  have htrace : WordTrace (prefixWord ++ tailWord_5836837) baseStart_5836837 baseEnd_5836837 := by
    simpa [prefixWord, tailWord_5836837, baseEnd_5836837] using wordTrace_append hprefix tailTrace_5836837
  have hstable : (prefixWord ++ tailWord_5836837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836837).length < 2 ^ (prefixWord ++ tailWord_5836837).sum := by decide
  have hdescent : baseEnd_5836837 < baseStart_5836837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836847 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_5836847 : Nat := 118140960795 + 5836847 * 2 ^ 59
def prefixEnd_5836847 : Nat := 4983230072969 + 3 ^ 40 * 5836847 * 2
def baseEnd_5836847 : Nat := 2997108017753630042969335

theorem tailTrace_5836847 : CollatzResearch.WordTrace tailWord_5836847 prefixEnd_5836847 2997108017753630042969335 := by
  unfold tailWord_5836847
  simp only [CollatzResearch.WordTrace]
  refine ⟨212887299485107647949100795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141924866323405098632733863 212887299485107647949100795)
  ·
    refine ⟨319330949227661471923651193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212887299485107647949100795 319330949227661471923651193)
    ·
      refine ⟨239498211920746103942738395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319330949227661471923651193 239498211920746103942738395)
      ·
        refine ⟨359247317881119155914107593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239498211920746103942738395 359247317881119155914107593)
        ·
          refine ⟨269435488410839366935580695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359247317881119155914107593 269435488410839366935580695)
          ·
            refine ⟨404153232616259050403371043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269435488410839366935580695 404153232616259050403371043)
            ·
              refine ⟨606229848924388575605056565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404153232616259050403371043 606229848924388575605056565)
              ·
                refine ⟨56834048336661428962974053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 606229848924388575605056565 56834048336661428962974053)
                ·
                  refine ⟨10656384063124017930557635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56834048336661428962974053 10656384063124017930557635)
                  ·
                    refine ⟨15984576094686026895836453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10656384063124017930557635 15984576094686026895836453)
                    ·
                      refine ⟨2997108017753630042969335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15984576094686026895836453 2997108017753630042969335)
                      ·
                        rfl

theorem cell23_5836847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_5836847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836847 prefixEnd_5836847 := by exact prefixLift 5836847
  have htrace : WordTrace (prefixWord ++ tailWord_5836847) baseStart_5836847 baseEnd_5836847 := by
    simpa [prefixWord, tailWord_5836847, baseEnd_5836847] using wordTrace_append hprefix tailTrace_5836847
  have hstable : (prefixWord ++ tailWord_5836847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836847).length < 2 ^ (prefixWord ++ tailWord_5836847).sum := by decide
  have hdescent : baseEnd_5836847 < baseStart_5836847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836854 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5836854 : Nat := 118140960795 + 5836854 * 2 ^ 59
def prefixEnd_5836854 : Nat := 4983230072969 + 3 ^ 40 * 5836854 * 2
def baseEnd_5836854 : Nat := 2997111612118211515581803

theorem tailTrace_5836854 : CollatzResearch.WordTrace tailWord_5836854 prefixEnd_5836854 2997111612118211515581803 := by
  unfold tailWord_5836854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13305472174755143009037851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141925036530721525429737077 13305472174755143009037851)
  ·
    refine ⟨19958208262132714513556777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13305472174755143009037851 19958208262132714513556777)
    ·
      refine ⟨14968656196599535885167583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19958208262132714513556777 14968656196599535885167583)
      ·
        refine ⟨22452984294899303827751375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14968656196599535885167583 22452984294899303827751375)
        ·
          refine ⟨33679476442348955741627063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22452984294899303827751375 33679476442348955741627063)
          ·
            refine ⟨50519214663523433612440595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33679476442348955741627063 50519214663523433612440595)
            ·
              refine ⟨75778821995285150418660893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50519214663523433612440595 75778821995285150418660893)
              ·
                refine ⟨28417058248231931406997835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75778821995285150418660893 28417058248231931406997835)
                ·
                  refine ⟨42625587372347897110496753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28417058248231931406997835 42625587372347897110496753)
                  ·
                    refine ⟨31969190529260922832872565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42625587372347897110496753 31969190529260922832872565)
                    ·
                      refine ⟨2997111612118211515581803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31969190529260922832872565 2997111612118211515581803)
                      ·
                        rfl

theorem cell23_5836854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5836854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836854 prefixEnd_5836854 := by exact prefixLift 5836854
  have htrace : WordTrace (prefixWord ++ tailWord_5836854) baseStart_5836854 baseEnd_5836854 := by
    simpa [prefixWord, tailWord_5836854, baseEnd_5836854] using wordTrace_append hprefix tailTrace_5836854
  have hstable : (prefixWord ++ tailWord_5836854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836854).length < 2 ^ (prefixWord ++ tailWord_5836854).sum := by decide
  have hdescent : baseEnd_5836854 < baseStart_5836854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836864 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2]
def baseStart_5836864 : Nat := 118140960795 + 5836864 * 2 ^ 59
def prefixEnd_5836864 : Nat := 4983230072969 + 3 ^ 40 * 5836864 * 2
def baseEnd_5836864 : Nat := 2997116746924756476456757

theorem tailTrace_5836864 : CollatzResearch.WordTrace tailWord_5836864 prefixEnd_5836864 2997116746924756476456757 := by
  unfold tailWord_5836864
  simp only [CollatzResearch.WordTrace]
  refine ⟨106443959763023029926234823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141925279684030706568313097 106443959763023029926234823)
  ·
    refine ⟨159665939644534544889352235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106443959763023029926234823 159665939644534544889352235)
    ·
      refine ⟨239498909466801817334028353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159665939644534544889352235 239498909466801817334028353)
      ·
        refine ⟨179624182100101363000521265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239498909466801817334028353 179624182100101363000521265)
        ·
          refine ⟨134718136575076022250390949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179624182100101363000521265 134718136575076022250390949)
          ·
            refine ⟨25259650607826754171948303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134718136575076022250390949 25259650607826754171948303)
            ·
              refine ⟨37889475911740131257922455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25259650607826754171948303 37889475911740131257922455)
              ·
                refine ⟨56834213867610196886883683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37889475911740131257922455 56834213867610196886883683)
                ·
                  refine ⟨85251320801415295330325525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56834213867610196886883683 85251320801415295330325525)
                  ·
                    refine ⟨3996155662566341968609009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85251320801415295330325525 3996155662566341968609009)
                    ·
                      refine ⟨2997116746924756476456757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996155662566341968609009 2997116746924756476456757)
                      ·
                        rfl

theorem cell23_5836864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_5836864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836864 prefixEnd_5836864 := by exact prefixLift 5836864
  have htrace : WordTrace (prefixWord ++ tailWord_5836864) baseStart_5836864 baseEnd_5836864 := by
    simpa [prefixWord, tailWord_5836864, baseEnd_5836864] using wordTrace_append hprefix tailTrace_5836864
  have hstable : (prefixWord ++ tailWord_5836864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836864).length < 2 ^ (prefixWord ++ tailWord_5836864).sum := by decide
  have hdescent : baseEnd_5836864 < baseStart_5836864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836921 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 6]
def baseStart_5836921 : Nat := 118140960795 + 5836921 * 2 ^ 59
def prefixEnd_5836921 : Nat := 4983230072969 + 3 ^ 40 * 5836921 * 2
def baseEnd_5836921 : Nat := 333016223924673639271555

theorem tailTrace_5836921 : CollatzResearch.WordTrace tailWord_5836921 prefixEnd_5836921 333016223924673639271555 := by
  unfold tailWord_5836921
  simp only [CollatzResearch.WordTrace]
  refine ⟨212889998486839558587294617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141926665657893039058196411 212889998486839558587294617)
  ·
    refine ⟨159667498865129668940470963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212889998486839558587294617 159667498865129668940470963)
    ·
      refine ⟨239501248297694503410706445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159667498865129668940470963 239501248297694503410706445)
      ·
        refine ⟨89812968111635438779014917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239501248297694503410706445 89812968111635438779014917)
        ·
          refine ⟨16839931520931644771065297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89812968111635438779014917 16839931520931644771065297)
          ·
            refine ⟨12629948640698733578298973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16839931520931644771065297 12629948640698733578298973)
            ·
              refine ⟨4736230740262025091862115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12629948640698733578298973 4736230740262025091862115)
              ·
                refine ⟨7104346110393037637793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736230740262025091862115 7104346110393037637793173)
                ·
                  refine ⟨333016223924673639271555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7104346110393037637793173 333016223924673639271555)
                  ·
                    rfl

theorem cell23_5836921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 6].length) (baseStart_5836921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836921 prefixEnd_5836921 := by exact prefixLift 5836921
  have htrace : WordTrace (prefixWord ++ tailWord_5836921) baseStart_5836921 baseEnd_5836921 := by
    simpa [prefixWord, tailWord_5836921, baseEnd_5836921] using wordTrace_append hprefix tailTrace_5836921
  have hstable : (prefixWord ++ tailWord_5836921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836921).length < 2 ^ (prefixWord ++ tailWord_5836921).sum := by decide
  have hdescent : baseEnd_5836921 < baseStart_5836921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836931 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 3]
def baseStart_5836931 : Nat := 118140960795 + 5836931 * 2 ^ 59
def prefixEnd_5836931 : Nat := 4983230072969 + 3 ^ 40 * 5836931 * 2
def baseEnd_5836931 : Nat := 2997151150128607714318949

theorem tailTrace_5836931 : CollatzResearch.WordTrace tailWord_5836931 prefixEnd_5836931 2997151150128607714318949 := by
  unfold tailWord_5836931
  simp only [CollatzResearch.WordTrace]
  refine ⟨212890363216803330295158647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141926908811202220196772431 212890363216803330295158647)
  ·
    refine ⟨319335544825204995442737971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212890363216803330295158647 319335544825204995442737971)
    ·
      refine ⟨479003317237807493164106957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319335544825204995442737971 479003317237807493164106957)
      ·
        refine ⟨179626243964177809936540109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479003317237807493164106957 179626243964177809936540109)
        ·
          refine ⟨67359841486566678726202541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179626243964177809936540109 67359841486566678726202541)
          ·
            refine ⟨25259940557462504522325953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67359841486566678726202541 25259940557462504522325953)
            ·
              refine ⟨18944955418096878391744465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25259940557462504522325953 18944955418096878391744465)
              ·
                refine ⟨14208716563572658793808349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18944955418096878391744465 14208716563572658793808349)
                ·
                  refine ⟨5328268711339747047678131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14208716563572658793808349 5328268711339747047678131)
                  ·
                    refine ⟨7992403067009620571517197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328268711339747047678131 7992403067009620571517197)
                    ·
                      refine ⟨2997151150128607714318949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992403067009620571517197 2997151150128607714318949)
                      ·
                        rfl

theorem cell23_5836931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_5836931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836931 prefixEnd_5836931 := by exact prefixLift 5836931
  have htrace : WordTrace (prefixWord ++ tailWord_5836931) baseStart_5836931 baseEnd_5836931 := by
    simpa [prefixWord, tailWord_5836931, baseEnd_5836931] using wordTrace_append hprefix tailTrace_5836931
  have hstable : (prefixWord ++ tailWord_5836931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836931).length < 2 ^ (prefixWord ++ tailWord_5836931).sum := by decide
  have hdescent : baseEnd_5836931 < baseStart_5836931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836942 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_5836942 : Nat := 118140960795 + 5836942 * 2 ^ 59
def prefixEnd_5836942 : Nat := 4983230072969 + 3 ^ 40 * 5836942 * 2
def baseEnd_5836942 : Nat := 999052266138602390427133

theorem tailTrace_5836942 : CollatzResearch.WordTrace tailWord_5836942 prefixEnd_5836942 999052266138602390427133 := by
  unfold tailWord_5836942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26611345552470434896726135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141927176279842319449206053 26611345552470434896726135)
  ·
    refine ⟨39917018328705652345089203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26611345552470434896726135 39917018328705652345089203)
    ·
      refine ⟨59875527493058478517633805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39917018328705652345089203 59875527493058478517633805)
      ·
        refine ⟨22453322809896929444112677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59875527493058478517633805 22453322809896929444112677)
        ·
          refine ⟨4209998026855674270771127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22453322809896929444112677 4209998026855674270771127)
          ·
            refine ⟨6314997040283511406156691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209998026855674270771127 6314997040283511406156691)
            ·
              refine ⟨9472495560425267109235037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314997040283511406156691 9472495560425267109235037)
              ·
                refine ⟨3552185835159475165963139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9472495560425267109235037 3552185835159475165963139)
                ·
                  refine ⟨5328278752739212748944709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552185835159475165963139 5328278752739212748944709)
                  ·
                    refine ⟨999052266138602390427133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328278752739212748944709 999052266138602390427133)
                    ·
                      rfl

theorem cell23_5836942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_5836942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836942 prefixEnd_5836942 := by exact prefixLift 5836942
  have htrace : WordTrace (prefixWord ++ tailWord_5836942) baseStart_5836942 baseEnd_5836942 := by
    simpa [prefixWord, tailWord_5836942, baseEnd_5836942] using wordTrace_append hprefix tailTrace_5836942
  have hstable : (prefixWord ++ tailWord_5836942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836942).length < 2 ^ (prefixWord ++ tailWord_5836942).sum := by decide
  have hdescent : baseEnd_5836942 < baseStart_5836942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
