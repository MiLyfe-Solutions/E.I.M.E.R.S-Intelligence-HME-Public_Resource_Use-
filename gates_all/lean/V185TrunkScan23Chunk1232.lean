import V185TrunkScan23Chunk1231

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7300257 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7300257 : Nat := 118140960795 + 7300257 * 2 ^ 59
def prefixEnd_7300257 : Nat := 4983230072969 + 3 ^ 40 * 7300257 * 2
def baseEnd_7300257 : Nat := 3748540742349749444614235

theorem tailTrace_7300257 : CollatzResearch.WordTrace tailWord_7300257 prefixEnd_7300257 3748540742349749444614235 := by
  unfold tailWord_7300257
  simp only [CollatzResearch.WordTrace]
  refine ⟨266262247113423148479115025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177508164742282098986076683 266262247113423148479115025)
  ·
    refine ⟨199696685335067361359336269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266262247113423148479115025 199696685335067361359336269)
    ·
      refine ⟨74886257000650260509751101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199696685335067361359336269 74886257000650260509751101)
      ·
        refine ⟨28082346375243847691156663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74886257000650260509751101 28082346375243847691156663)
        ·
          refine ⟨42123519562865771536734995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28082346375243847691156663 42123519562865771536734995)
          ·
            refine ⟨63185279344298657305102493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42123519562865771536734995 63185279344298657305102493)
            ·
              refine ⟨23694479754111996489413435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63185279344298657305102493 23694479754111996489413435)
              ·
                refine ⟨35541719631167994734120153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23694479754111996489413435 35541719631167994734120153)
                ·
                  refine ⟨26656289723375996050590115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35541719631167994734120153 26656289723375996050590115)
                  ·
                    refine ⟨39984434585063994075885173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26656289723375996050590115 39984434585063994075885173)
                    ·
                      refine ⟨3748540742349749444614235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39984434585063994075885173 3748540742349749444614235)
                      ·
                        rfl

theorem cell23_7300257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7300257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300257 prefixEnd_7300257 := by exact prefixLift 7300257
  have htrace : WordTrace (prefixWord ++ tailWord_7300257) baseStart_7300257 baseEnd_7300257 := by
    simpa [prefixWord, tailWord_7300257, baseEnd_7300257] using wordTrace_append hprefix tailTrace_7300257
  have hstable : (prefixWord ++ tailWord_7300257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300257).length < 2 ^ (prefixWord ++ tailWord_7300257).sum := by decide
  have hdescent : baseEnd_7300257 < baseStart_7300257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_7300280 : Nat := 118140960795 + 7300280 * 2 ^ 59
def prefixEnd_7300280 : Nat := 4983230072969 + 3 ^ 40 * 7300280 * 2
def baseEnd_7300280 : Nat := 3748552552404802854626629

theorem tailTrace_7300280 : CollatzResearch.WordTrace tailWord_7300280 prefixEnd_7300280 3748552552404802854626629 := by
  unfold tailWord_7300280
  simp only [CollatzResearch.WordTrace]
  refine ⟨133131542996169911703601147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177508723994893215604801529 133131542996169911703601147)
  ·
    refine ⟨199697314494254867555401721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133131542996169911703601147 199697314494254867555401721)
    ·
      refine ⟨149772985870691150666551291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199697314494254867555401721 149772985870691150666551291)
      ·
        refine ⟨224659478806036725999826937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149772985870691150666551291 224659478806036725999826937)
        ·
          refine ⟨168494609104527544499870203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224659478806036725999826937 168494609104527544499870203)
          ·
            refine ⟨252741913656791316749805305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168494609104527544499870203 252741913656791316749805305)
            ·
              refine ⟨189556435242593487562353979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252741913656791316749805305 189556435242593487562353979)
              ·
                refine ⟨284334652863890231343530969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189556435242593487562353979 284334652863890231343530969)
                ·
                  refine ⟨213250989647917673507648227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284334652863890231343530969 213250989647917673507648227)
                  ·
                    refine ⟨319876484471876510261472341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213250989647917673507648227 319876484471876510261472341)
                    ·
                      refine ⟨3748552552404802854626629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319876484471876510261472341 3748552552404802854626629)
                      ·
                        rfl

theorem cell23_7300280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_7300280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300280 prefixEnd_7300280 := by exact prefixLift 7300280
  have htrace : WordTrace (prefixWord ++ tailWord_7300280) baseStart_7300280 baseEnd_7300280 := by
    simpa [prefixWord, tailWord_7300280, baseEnd_7300280] using wordTrace_append hprefix tailTrace_7300280
  have hstable : (prefixWord ++ tailWord_7300280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300280).length < 2 ^ (prefixWord ++ tailWord_7300280).sum := by decide
  have hdescent : baseEnd_7300280 < baseStart_7300280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300287 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_7300287 : Nat := 118140960795 + 7300287 * 2 ^ 59
def prefixEnd_7300287 : Nat := 4983230072969 + 3 ^ 40 * 7300287 * 2
def baseEnd_7300287 : Nat := 3748556146769384327239097

theorem tailTrace_7300287 : CollatzResearch.WordTrace tailWord_7300287 prefixEnd_7300287 3748556146769384327239097 := by
  unfold tailWord_7300287
  simp only [CollatzResearch.WordTrace]
  refine ⟨266263341303314463602707115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177508894202209642401804743 266263341303314463602707115)
  ·
    refine ⟨399395011954971695404060673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266263341303314463602707115 399395011954971695404060673)
    ·
      refine ⟨299546258966228771553045505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399395011954971695404060673 299546258966228771553045505)
      ·
        refine ⟨224659694224671578664784129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299546258966228771553045505 224659694224671578664784129)
        ·
          refine ⟨168494770668503683998588097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224659694224671578664784129 168494770668503683998588097)
          ·
            refine ⟨126371078001377762998941073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168494770668503683998588097 126371078001377762998941073)
            ·
              refine ⟨94778308501033322249205805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126371078001377762998941073 94778308501033322249205805)
              ·
                refine ⟨35541865687887495843452177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94778308501033322249205805 35541865687887495843452177)
                ·
                  refine ⟨26656399265915621882589133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35541865687887495843452177 26656399265915621882589133)
                  ·
                    refine ⟨9996149724718358205970925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26656399265915621882589133 9996149724718358205970925)
                    ·
                      refine ⟨3748556146769384327239097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996149724718358205970925 3748556146769384327239097)
                      ·
                        rfl

theorem cell23_7300287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_7300287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300287 prefixEnd_7300287 := by exact prefixLift 7300287
  have htrace : WordTrace (prefixWord ++ tailWord_7300287) baseStart_7300287 baseEnd_7300287 := by
    simpa [prefixWord, tailWord_7300287, baseEnd_7300287] using wordTrace_append hprefix tailTrace_7300287
  have hstable : (prefixWord ++ tailWord_7300287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300287).length < 2 ^ (prefixWord ++ tailWord_7300287).sum := by decide
  have hdescent : baseEnd_7300287 < baseStart_7300287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300288 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2]
def baseStart_7300288 : Nat := 118140960795 + 7300288 * 2 ^ 59
def prefixEnd_7300288 : Nat := 4983230072969 + 3 ^ 40 * 7300288 * 2
def baseEnd_7300288 : Nat := 3748556660250038823326593

theorem tailTrace_7300288 : CollatzResearch.WordTrace tailWord_7300288 prefixEnd_7300288 3748556660250038823326593 := by
  unfold tailWord_7300288
  simp only [CollatzResearch.WordTrace]
  refine ⟨133131688888155420386746759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177508918517540560515662345 133131688888155420386746759)
  ·
    refine ⟨199697533332233130580120139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133131688888155420386746759 199697533332233130580120139)
    ·
      refine ⟨299546299998349695870180209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199697533332233130580120139 299546299998349695870180209)
      ·
        refine ⟨224659724998762271902635157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299546299998349695870180209 224659724998762271902635157)
        ·
          refine ⟨10530924609316981495436023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224659724998762271902635157 10530924609316981495436023)
          ·
            refine ⟨15796386913975472243154035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530924609316981495436023 15796386913975472243154035)
            ·
              refine ⟨23694580370963208364731053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796386913975472243154035 23694580370963208364731053)
              ·
                refine ⟨8885467639111203136774145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23694580370963208364731053 8885467639111203136774145)
                ·
                  refine ⟨6664100729333402352580609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885467639111203136774145 6664100729333402352580609)
                  ·
                    refine ⟨4998075547000051764435457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6664100729333402352580609 4998075547000051764435457)
                    ·
                      refine ⟨3748556660250038823326593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998075547000051764435457 3748556660250038823326593)
                      ·
                        rfl

theorem cell23_7300288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_7300288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300288 prefixEnd_7300288 := by exact prefixLift 7300288
  have htrace : WordTrace (prefixWord ++ tailWord_7300288) baseStart_7300288 baseEnd_7300288 := by
    simpa [prefixWord, tailWord_7300288, baseEnd_7300288] using wordTrace_append hprefix tailTrace_7300288
  have hstable : (prefixWord ++ tailWord_7300288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300288).length < 2 ^ (prefixWord ++ tailWord_7300288).sum := by decide
  have hdescent : baseEnd_7300288 < baseStart_7300288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300364 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_7300364 : Nat := 118140960795 + 7300364 * 2 ^ 59
def prefixEnd_7300364 : Nat := 4983230072969 + 3 ^ 40 * 7300364 * 2
def baseEnd_7300364 : Nat := 3748595684779780525976243

theorem tailTrace_7300364 : CollatzResearch.WordTrace tailWord_7300364 prefixEnd_7300364 3748595684779780525976243 := by
  unfold tailWord_7300364
  simp only [CollatzResearch.WordTrace]
  refine ⟨133133074862017752876630073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177510766482690337168840097 133133074862017752876630073)
  ·
    refine ⟨99849806146513314657472555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133133074862017752876630073 99849806146513314657472555)
    ·
      refine ⟨149774709219769971986208833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99849806146513314657472555 149774709219769971986208833)
      ·
        refine ⟨112331031914827478989656625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149774709219769971986208833 112331031914827478989656625)
        ·
          refine ⟨84248273936120609242242469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112331031914827478989656625 84248273936120609242242469)
          ·
            refine ⟨15796551363022614232920463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84248273936120609242242469 15796551363022614232920463)
            ·
              refine ⟨23694827044533921349380695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796551363022614232920463 23694827044533921349380695)
              ·
                refine ⟨35542240566800882024071043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23694827044533921349380695 35542240566800882024071043)
                ·
                  refine ⟨53313360850201323036106565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35542240566800882024071043 53313360850201323036106565)
                  ·
                    refine ⟨9996255159412748069269981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53313360850201323036106565 9996255159412748069269981)
                    ·
                      refine ⟨3748595684779780525976243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996255159412748069269981 3748595684779780525976243)
                      ·
                        rfl

theorem cell23_7300364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_7300364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300364 prefixEnd_7300364 := by exact prefixLift 7300364
  have htrace : WordTrace (prefixWord ++ tailWord_7300364) baseStart_7300364 baseEnd_7300364 := by
    simpa [prefixWord, tailWord_7300364, baseEnd_7300364] using wordTrace_append hprefix tailTrace_7300364
  have hstable : (prefixWord ++ tailWord_7300364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300364).length < 2 ^ (prefixWord ++ tailWord_7300364).sum := by decide
  have hdescent : baseEnd_7300364 < baseStart_7300364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300377 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_7300377 : Nat := 118140960795 + 7300377 * 2 ^ 59
def prefixEnd_7300377 : Nat := 4983230072969 + 3 ^ 40 * 7300377 * 2
def baseEnd_7300377 : Nat := 3748602360028288975113683

theorem tailTrace_7300377 : CollatzResearch.WordTrace tailWord_7300377 prefixEnd_7300377 3748602360028288975113683 := by
  unfold tailWord_7300377
  simp only [CollatzResearch.WordTrace]
  refine ⟨266266623872988408973483385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177511082581992272648988923 266266623872988408973483385)
  ·
    refine ⟨199699967904741306730112539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266266623872988408973483385 199699967904741306730112539)
    ·
      refine ⟨299549951857111960095168809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199699967904741306730112539 299549951857111960095168809)
      ·
        refine ⟨224662463892833970071376607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299549951857111960095168809 224662463892833970071376607)
        ·
          refine ⟨336993695839250955107064911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224662463892833970071376607 336993695839250955107064911)
          ·
            refine ⟨505490543758876432660597367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336993695839250955107064911 505490543758876432660597367)
            ·
              refine ⟨758235815638314648990896051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505490543758876432660597367 758235815638314648990896051)
              ·
                refine ⟨1137353723457471973486344077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758235815638314648990896051 1137353723457471973486344077)
                ·
                  refine ⟨426507646296551990057379029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137353723457471973486344077 426507646296551990057379029)
                  ·
                    refine ⟨9996272960075437266969821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 426507646296551990057379029 9996272960075437266969821)
                    ·
                      refine ⟨3748602360028288975113683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996272960075437266969821 3748602360028288975113683)
                      ·
                        rfl

theorem cell23_7300377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_7300377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300377 prefixEnd_7300377 := by exact prefixLift 7300377
  have htrace : WordTrace (prefixWord ++ tailWord_7300377) baseStart_7300377 baseEnd_7300377 := by
    simpa [prefixWord, tailWord_7300377, baseEnd_7300377] using wordTrace_append hprefix tailTrace_7300377
  have hstable : (prefixWord ++ tailWord_7300377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300377).length < 2 ^ (prefixWord ++ tailWord_7300377).sum := by decide
  have hdescent : baseEnd_7300377 < baseStart_7300377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300384 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 8]
def baseStart_7300384 : Nat := 118140960795 + 7300384 * 2 ^ 59
def prefixEnd_7300384 : Nat := 4983230072969 + 3 ^ 40 * 7300384 * 2
def baseEnd_7300384 : Nat := 416511772710318938636239

theorem tailTrace_7300384 : CollatzResearch.WordTrace tailWord_7300384 prefixEnd_7300384 416511772710318938636239 := by
  unfold tailWord_7300384
  simp only [CollatzResearch.WordTrace]
  refine ⟨133133439591981524584494103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177511252789308699445992137 133133439591981524584494103)
  ·
    refine ⟨199700159387972286876741155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133133439591981524584494103 199700159387972286876741155)
    ·
      refine ⟨299550239081958430315111733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199700159387972286876741155 299550239081958430315111733)
      ·
        refine ⟨28082834913933602842041725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299550239081958430315111733 28082834913933602842041725)
        ·
          refine ⟨10531063092725101065765647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28082834913933602842041725 10531063092725101065765647)
          ·
            refine ⟨15796594639087651598648471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531063092725101065765647 15796594639087651598648471)
            ·
              refine ⟨23694891958631477397972707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796594639087651598648471 23694891958631477397972707)
              ·
                refine ⟨35542337937947216096959061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23694891958631477397972707 35542337937947216096959061)
                ·
                  refine ⟨416511772710318938636239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35542337937947216096959061 416511772710318938636239)
                  ·
                    rfl

theorem cell23_7300384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_7300384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300384 prefixEnd_7300384 := by exact prefixLift 7300384
  have htrace : WordTrace (prefixWord ++ tailWord_7300384) baseStart_7300384 baseEnd_7300384 := by
    simpa [prefixWord, tailWord_7300384, baseEnd_7300384] using wordTrace_append hprefix tailTrace_7300384
  have hstable : (prefixWord ++ tailWord_7300384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300384).length < 2 ^ (prefixWord ++ tailWord_7300384).sum := by decide
  have hdescent : baseEnd_7300384 < baseStart_7300384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300387 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_7300387 : Nat := 118140960795 + 7300387 * 2 ^ 59
def prefixEnd_7300387 : Nat := 4983230072969 + 3 ^ 40 * 7300387 * 2
def baseEnd_7300387 : Nat := 3748607494834833935988637

theorem tailTrace_7300387 : CollatzResearch.WordTrace tailWord_7300387 prefixEnd_7300387 3748607494834833935988637 := by
  unfold tailWord_7300387
  simp only [CollatzResearch.WordTrace]
  refine ⟨266266988602952180681347415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177511325735301453787564943 266266988602952180681347415)
  ·
    refine ⟨399400482904428271022021123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266266988602952180681347415 399400482904428271022021123)
    ·
      refine ⟨599100724356642406533031685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399400482904428271022021123 599100724356642406533031685)
      ·
        refine ⟨112331385816870451224943441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599100724356642406533031685 112331385816870451224943441)
        ·
          refine ⟨84248539362652838418707581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112331385816870451224943441 84248539362652838418707581)
          ·
            refine ⟨31593202260994814407015343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84248539362652838418707581 31593202260994814407015343)
            ·
              refine ⟨47389803391492221610523015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31593202260994814407015343 47389803391492221610523015)
              ·
                refine ⟨71084705087238332415784523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47389803391492221610523015 71084705087238332415784523)
                ·
                  refine ⟨106627057630857498623676785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71084705087238332415784523 106627057630857498623676785)
                  ·
                    refine ⟨79970293223143123967757589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106627057630857498623676785 79970293223143123967757589)
                    ·
                      refine ⟨3748607494834833935988637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79970293223143123967757589 3748607494834833935988637)
                      ·
                        rfl

theorem cell23_7300387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_7300387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300387 prefixEnd_7300387 := by exact prefixLift 7300387
  have htrace : WordTrace (prefixWord ++ tailWord_7300387) baseStart_7300387 baseEnd_7300387 := by
    simpa [prefixWord, tailWord_7300387, baseEnd_7300387] using wordTrace_append hprefix tailTrace_7300387
  have hstable : (prefixWord ++ tailWord_7300387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300387).length < 2 ^ (prefixWord ++ tailWord_7300387).sum := by decide
  have hdescent : baseEnd_7300387 < baseStart_7300387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300401 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 6]
def baseStart_7300401 : Nat := 118140960795 + 7300401 * 2 ^ 59
def prefixEnd_7300401 : Nat := 4983230072969 + 3 ^ 40 * 7300401 * 2
def baseEnd_7300401 : Nat := 416512742618221875690397

theorem tailTrace_7300401 : CollatzResearch.WordTrace tailWord_7300401 prefixEnd_7300401 416512742618221875690397 := by
  unfold tailWord_7300401
  simp only [CollatzResearch.WordTrace]
  refine ⟨266267499224901461072357057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177511666149934307381571371 266267499224901461072357057)
  ·
    refine ⟨199700624418676095804267793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266267499224901461072357057 199700624418676095804267793)
    ·
      refine ⟨149775468314007071853200845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199700624418676095804267793 149775468314007071853200845)
      ·
        refine ⟨56165800617752651944950317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149775468314007071853200845 56165800617752651944950317)
        ·
          refine ⟨21062175231657244479356369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56165800617752651944950317 21062175231657244479356369)
          ·
            refine ⟨15796631423742933359517277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21062175231657244479356369 15796631423742933359517277)
            ·
              refine ⟨5923736783903600009818979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15796631423742933359517277 5923736783903600009818979)
              ·
                refine ⟨8885605175855400014728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923736783903600009818979 8885605175855400014728469)
                ·
                  refine ⟨416512742618221875690397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8885605175855400014728469 416512742618221875690397)
                  ·
                    rfl

theorem cell23_7300401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 6].length) (baseStart_7300401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300401 prefixEnd_7300401 := by exact prefixLift 7300401
  have htrace : WordTrace (prefixWord ++ tailWord_7300401) baseStart_7300401 baseEnd_7300401 := by
    simpa [prefixWord, tailWord_7300401, baseEnd_7300401] using wordTrace_append hprefix tailTrace_7300401
  have hstable : (prefixWord ++ tailWord_7300401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300401).length < 2 ^ (prefixWord ++ tailWord_7300401).sum := by decide
  have hdescent : baseEnd_7300401 < baseStart_7300401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300404 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7300404 : Nat := 118140960795 + 7300404 * 2 ^ 59
def prefixEnd_7300404 : Nat := 4983230072969 + 3 ^ 40 * 7300404 * 2
def baseEnd_7300404 : Nat := 3748616224005960369476059

theorem tailTrace_7300404 : CollatzResearch.WordTrace tailWord_7300404 prefixEnd_7300404 3748616224005960369476059 := by
  unfold tailWord_7300404
  simp only [CollatzResearch.WordTrace]
  refine ⟨133133804321945296292358133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177511739095927061723144177 133133804321945296292358133)
  ·
    refine ⟨12481294155182371527408575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133133804321945296292358133 12481294155182371527408575)
    ·
      refine ⟨18721941232773557291112863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481294155182371527408575 18721941232773557291112863)
      ·
        refine ⟨28082911849160335936669295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721941232773557291112863 28082911849160335936669295)
        ·
          refine ⟨42124367773740503905003943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28082911849160335936669295 42124367773740503905003943)
          ·
            refine ⟨63186551660610755857505915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42124367773740503905003943 63186551660610755857505915)
            ·
              refine ⟨94779827490916133786258873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63186551660610755857505915 94779827490916133786258873)
              ·
                refine ⟨71084870618187100339694155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94779827490916133786258873 71084870618187100339694155)
                ·
                  refine ⟨106627305927280650509541233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71084870618187100339694155 106627305927280650509541233)
                  ·
                    refine ⟨79970479445460487882155925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106627305927280650509541233 79970479445460487882155925)
                    ·
                      refine ⟨3748616224005960369476059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79970479445460487882155925 3748616224005960369476059)
                      ·
                        rfl

theorem cell23_7300404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7300404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300404 prefixEnd_7300404 := by exact prefixLift 7300404
  have htrace : WordTrace (prefixWord ++ tailWord_7300404) baseStart_7300404 baseEnd_7300404 := by
    simpa [prefixWord, tailWord_7300404, baseEnd_7300404] using wordTrace_append hprefix tailTrace_7300404
  have hstable : (prefixWord ++ tailWord_7300404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300404).length < 2 ^ (prefixWord ++ tailWord_7300404).sum := by decide
  have hdescent : baseEnd_7300404 < baseStart_7300404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300434 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7300434 : Nat := 118140960795 + 7300434 * 2 ^ 59
def prefixEnd_7300434 : Nat := 4983230072969 + 3 ^ 40 * 7300434 * 2
def baseEnd_7300434 : Nat := 3748631628425595252100921

theorem tailTrace_7300434 : CollatzResearch.WordTrace tailWord_7300434 prefixEnd_7300434 3748631628425595252100921 := by
  unfold tailWord_7300434
  simp only [CollatzResearch.WordTrace]
  refine ⟨66567175708445476927077089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177512468555854605138872237 66567175708445476927077089)
  ·
    refine ⟨49925381781334107695307817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66567175708445476927077089 49925381781334107695307817)
    ·
      refine ⟨37444036336000580771480863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49925381781334107695307817 37444036336000580771480863)
      ·
        refine ⟨56166054504000871157221295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37444036336000580771480863 56166054504000871157221295)
        ·
          refine ⟨84249081756001306735831943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56166054504000871157221295 84249081756001306735831943)
          ·
            refine ⟨126373622634001960103747915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84249081756001306735831943 126373622634001960103747915)
            ·
              refine ⟨189560433951002940155621873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126373622634001960103747915 189560433951002940155621873)
              ·
                refine ⟨142170325463252205116716405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189560433951002940155621873 142170325463252205116716405)
                ·
                  refine ⟨13328468012179894229692163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142170325463252205116716405 13328468012179894229692163)
                  ·
                    refine ⟨19992702018269841344538245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13328468012179894229692163 19992702018269841344538245)
                    ·
                      refine ⟨3748631628425595252100921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19992702018269841344538245 3748631628425595252100921)
                      ·
                        rfl

theorem cell23_7300434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7300434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300434 prefixEnd_7300434 := by exact prefixLift 7300434
  have htrace : WordTrace (prefixWord ++ tailWord_7300434) baseStart_7300434 baseEnd_7300434 := by
    simpa [prefixWord, tailWord_7300434, baseEnd_7300434] using wordTrace_append hprefix tailTrace_7300434
  have hstable : (prefixWord ++ tailWord_7300434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300434).length < 2 ^ (prefixWord ++ tailWord_7300434).sum := by decide
  have hdescent : baseEnd_7300434 < baseStart_7300434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300464 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_7300464 : Nat := 118140960795 + 7300464 * 2 ^ 59
def prefixEnd_7300464 : Nat := 4983230072969 + 3 ^ 40 * 7300464 * 2
def baseEnd_7300464 : Nat := 3748647032845230134725783

theorem tailTrace_7300464 : CollatzResearch.WordTrace tailWord_7300464 prefixEnd_7300464 3748647032845230134725783 := by
  unfold tailWord_7300464
  simp only [CollatzResearch.WordTrace]
  refine ⟨133134898511836611415950223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177513198015782148554600297 133134898511836611415950223)
  ·
    refine ⟨199702347767754917123925335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133134898511836611415950223 199702347767754917123925335)
    ·
      refine ⟨299553521651632375685888003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199702347767754917123925335 299553521651632375685888003)
      ·
        refine ⟨449330282477448563528832005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299553521651632375685888003 449330282477448563528832005)
        ·
          refine ⟨84249427964521605661656001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449330282477448563528832005 84249427964521605661656001)
          ·
            refine ⟨63187070973391204246242001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84249427964521605661656001 63187070973391204246242001)
            ·
              refine ⟨47390303230043403184681501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63187070973391204246242001 47390303230043403184681501)
              ·
                refine ⟨17771363711266276194255563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47390303230043403184681501 17771363711266276194255563)
                ·
                  refine ⟨26657045566899414291383345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17771363711266276194255563 26657045566899414291383345)
                  ·
                    refine ⟨19992784175174560718537509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26657045566899414291383345 19992784175174560718537509)
                    ·
                      refine ⟨3748647032845230134725783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19992784175174560718537509 3748647032845230134725783)
                      ·
                        rfl

theorem cell23_7300464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_7300464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300464 prefixEnd_7300464 := by exact prefixLift 7300464
  have htrace : WordTrace (prefixWord ++ tailWord_7300464) baseStart_7300464 baseEnd_7300464 := by
    simpa [prefixWord, tailWord_7300464, baseEnd_7300464] using wordTrace_append hprefix tailTrace_7300464
  have hstable : (prefixWord ++ tailWord_7300464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300464).length < 2 ^ (prefixWord ++ tailWord_7300464).sum := by decide
  have hdescent : baseEnd_7300464 < baseStart_7300464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300501 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_7300501 : Nat := 118140960795 + 7300501 * 2 ^ 59
def prefixEnd_7300501 : Nat := 4983230072969 + 3 ^ 40 * 7300501 * 2
def baseEnd_7300501 : Nat := 3748666031629446489963113

theorem tailTrace_7300501 : CollatzResearch.WordTrace tailWord_7300501 prefixEnd_7300501 3748666031629446489963113 := by
  unfold tailWord_7300501
  simp only [CollatzResearch.WordTrace]
  refine ⟨266271146524539178150997357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177514097683026118767331571 266271146524539178150997357)
  ·
    refine ⟨99851679946702191806624009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266271146524539178150997357 99851679946702191806624009)
    ·
      refine ⟨74888759960026643854968007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99851679946702191806624009 74888759960026643854968007)
      ·
        refine ⟨112333139940039965782452011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74888759960026643854968007 112333139940039965782452011)
        ·
          refine ⟨168499709910059948673678017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112333139940039965782452011 168499709910059948673678017)
          ·
            refine ⟨126374782432544961505258513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168499709910059948673678017 126374782432544961505258513)
            ·
              refine ⟨94781086824408721128943885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126374782432544961505258513 94781086824408721128943885)
              ·
                refine ⟨35542907559153270423353957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94781086824408721128943885 35542907559153270423353957)
                ·
                  refine ⟨6664295167341238204378867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35542907559153270423353957 6664295167341238204378867)
                  ·
                    refine ⟨9996442751011857306568301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6664295167341238204378867 9996442751011857306568301)
                    ·
                      refine ⟨3748666031629446489963113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996442751011857306568301 3748666031629446489963113)
                      ·
                        rfl

theorem cell23_7300501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_7300501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300501 prefixEnd_7300501 := by exact prefixLift 7300501
  have htrace : WordTrace (prefixWord ++ tailWord_7300501) baseStart_7300501 baseEnd_7300501 := by
    simpa [prefixWord, tailWord_7300501, baseEnd_7300501] using wordTrace_append hprefix tailTrace_7300501
  have hstable : (prefixWord ++ tailWord_7300501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300501).length < 2 ^ (prefixWord ++ tailWord_7300501).sum := by decide
  have hdescent : baseEnd_7300501 < baseStart_7300501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300507 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_7300507 : Nat := 118140960795 + 7300507 * 2 ^ 59
def prefixEnd_7300507 : Nat := 4983230072969 + 3 ^ 40 * 7300507 * 2
def baseEnd_7300507 : Nat := 3748669112513373466488085

theorem tailTrace_7300507 : CollatzResearch.WordTrace tailWord_7300507 prefixEnd_7300507 3748669112513373466488085 := by
  unfold tailWord_7300507
  simp only [CollatzResearch.WordTrace]
  refine ⟨266271365362517441175715775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177514243575011627450477183 266271365362517441175715775)
  ·
    refine ⟨399407048043776161763573663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266271365362517441175715775 399407048043776161763573663)
    ·
      refine ⟨599110572065664242645360495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399407048043776161763573663 599110572065664242645360495)
      ·
        refine ⟨898665858098496363968040743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599110572065664242645360495 898665858098496363968040743)
        ·
          refine ⟨1347998787147744545952061115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898665858098496363968040743 1347998787147744545952061115)
          ·
            refine ⟨2021998180721616818928091673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347998787147744545952061115 2021998180721616818928091673)
            ·
              refine ⟨1516498635541212614196068755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021998180721616818928091673 1516498635541212614196068755)
              ·
                refine ⟨2274747953311818921294103133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516498635541212614196068755 2274747953311818921294103133)
                ·
                  refine ⟨853030482491932095485288675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2274747953311818921294103133 853030482491932095485288675)
                  ·
                    refine ⟨1279545723737898143227933013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 853030482491932095485288675 1279545723737898143227933013)
                    ·
                      refine ⟨3748669112513373466488085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1279545723737898143227933013 3748669112513373466488085)
                      ·
                        rfl

theorem cell23_7300507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_7300507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300507 prefixEnd_7300507 := by exact prefixLift 7300507
  have htrace : WordTrace (prefixWord ++ tailWord_7300507) baseStart_7300507 baseEnd_7300507 := by
    simpa [prefixWord, tailWord_7300507, baseEnd_7300507] using wordTrace_append hprefix tailTrace_7300507
  have hstable : (prefixWord ++ tailWord_7300507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300507).length < 2 ^ (prefixWord ++ tailWord_7300507).sum := by decide
  have hdescent : baseEnd_7300507 < baseStart_7300507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300508 : List Nat := [2, 2, 3, 4, 1, 2, 1, 8]
def baseStart_7300508 : Nat := 118140960795 + 7300508 * 2 ^ 59
def prefixEnd_7300508 : Nat := 4983230072969 + 3 ^ 40 * 7300508 * 2
def baseEnd_7300508 : Nat := 138839615777556591206503

theorem tailTrace_7300508 : CollatzResearch.WordTrace tailWord_7300508 prefixEnd_7300508 138839615777556591206503 := by
  unfold tailWord_7300508
  simp only [CollatzResearch.WordTrace]
  refine ⟨133135700917756909173251089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177514267890342545564334785 133135700917756909173251089)
  ·
    refine ⟨99851775688317681879938317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133135700917756909173251089 99851775688317681879938317)
    ·
      refine ⟨37444415883119130704976869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99851775688317681879938317 37444415883119130704976869)
      ·
        refine ⟨7020827978084837007183163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37444415883119130704976869 7020827978084837007183163)
        ·
          refine ⟨10531241967127255510774745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020827978084837007183163 10531241967127255510774745)
          ·
            refine ⟨7898431475345441633081059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10531241967127255510774745 7898431475345441633081059)
            ·
              refine ⟨11847647213018162449621589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898431475345441633081059 11847647213018162449621589)
              ·
                refine ⟨138839615777556591206503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11847647213018162449621589 138839615777556591206503)
                ·
                  rfl

theorem cell23_7300508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 8].length) (baseStart_7300508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300508 prefixEnd_7300508 := by exact prefixLift 7300508
  have htrace : WordTrace (prefixWord ++ tailWord_7300508) baseStart_7300508 baseEnd_7300508 := by
    simpa [prefixWord, tailWord_7300508, baseEnd_7300508] using wordTrace_append hprefix tailTrace_7300508
  have hstable : (prefixWord ++ tailWord_7300508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300508).length < 2 ^ (prefixWord ++ tailWord_7300508).sum := by decide
  have hdescent : baseEnd_7300508 < baseStart_7300508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300544 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_7300544 : Nat := 118140960795 + 7300544 * 2 ^ 59
def prefixEnd_7300544 : Nat := 4983230072969 + 3 ^ 40 * 7300544 * 2
def baseEnd_7300544 : Nat := 3748688111297589821725415

theorem tailTrace_7300544 : CollatzResearch.WordTrace tailWord_7300544 prefixEnd_7300544 3748688111297589821725415 := by
  unfold tailWord_7300544
  simp only [CollatzResearch.WordTrace]
  refine ⟨133136357431691698247406343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177515143242255597663208457 133136357431691698247406343)
  ·
    refine ⟨199704536147537547371109515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133136357431691698247406343 199704536147537547371109515)
    ·
      refine ⟨299556804221306321056664273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199704536147537547371109515 299556804221306321056664273)
      ·
        refine ⟨224667603165979740792498205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299556804221306321056664273 224667603165979740792498205)
        ·
          refine ⟨84250351187242402797186827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224667603165979740792498205 84250351187242402797186827)
          ·
            refine ⟨126375526780863604195780241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84250351187242402797186827 126375526780863604195780241)
            ·
              refine ⟨94781645085647703146835181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126375526780863604195780241 94781645085647703146835181)
              ·
                refine ⟨35543116907117888680063193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94781645085647703146835181 35543116907117888680063193)
                ·
                  refine ⟨26657337680338416510047395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35543116907117888680063193 26657337680338416510047395)
                  ·
                    refine ⟨39986006520507624765071093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26657337680338416510047395 39986006520507624765071093)
                    ·
                      refine ⟨3748688111297589821725415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39986006520507624765071093 3748688111297589821725415)
                      ·
                        rfl

theorem cell23_7300544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_7300544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300544 prefixEnd_7300544 := by exact prefixLift 7300544
  have htrace : WordTrace (prefixWord ++ tailWord_7300544) baseStart_7300544 baseEnd_7300544 := by
    simpa [prefixWord, tailWord_7300544, baseEnd_7300544] using wordTrace_append hprefix tailTrace_7300544
  have hstable : (prefixWord ++ tailWord_7300544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300544).length < 2 ^ (prefixWord ++ tailWord_7300544).sum := by decide
  have hdescent : baseEnd_7300544 < baseStart_7300544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300546 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7300546 : Nat := 118140960795 + 7300546 * 2 ^ 59
def prefixEnd_7300546 : Nat := 4983230072969 + 3 ^ 40 * 7300546 * 2
def baseEnd_7300546 : Nat := 1249563046086299604633469

theorem tailTrace_7300546 : CollatzResearch.WordTrace tailWord_7300546 prefixEnd_7300546 1249563046086299604633469 := by
  unfold tailWord_7300546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66568196952344037709096373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177515191872917433890923661 66568196952344037709096373)
  ·
    refine ⟨6240768464282253535227785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66568196952344037709096373 6240768464282253535227785)
    ·
      refine ⟨4680576348211690151420839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6240768464282253535227785 4680576348211690151420839)
      ·
        refine ⟨7020864522317535227131259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680576348211690151420839 7020864522317535227131259)
        ·
          refine ⟨10531296783476302840696889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020864522317535227131259 10531296783476302840696889)
          ·
            refine ⟨7898472587607227130522667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10531296783476302840696889 7898472587607227130522667)
            ·
              refine ⟨11847708881410840695784001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898472587607227130522667 11847708881410840695784001)
              ·
                refine ⟨8885781661058130521838001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11847708881410840695784001 8885781661058130521838001)
                ·
                  refine ⟨6664336245793597891378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885781661058130521838001 6664336245793597891378501)
                  ·
                    refine ⟨1249563046086299604633469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664336245793597891378501 1249563046086299604633469)
                    ·
                      rfl

theorem cell23_7300546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7300546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300546 prefixEnd_7300546 := by exact prefixLift 7300546
  have htrace : WordTrace (prefixWord ++ tailWord_7300546) baseStart_7300546 baseEnd_7300546 := by
    simpa [prefixWord, tailWord_7300546, baseEnd_7300546] using wordTrace_append hprefix tailTrace_7300546
  have hstable : (prefixWord ++ tailWord_7300546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300546).length < 2 ^ (prefixWord ++ tailWord_7300546).sum := by decide
  have hdescent : baseEnd_7300546 < baseStart_7300546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300581 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 7]
def baseStart_7300581 : Nat := 118140960795 + 7300581 * 2 ^ 59
def prefixEnd_7300581 : Nat := 4983230072969 + 3 ^ 40 * 7300581 * 2
def baseEnd_7300581 : Nat := 416523012231311797440305

theorem tailTrace_7300581 : CollatzResearch.WordTrace tailWord_7300581 prefixEnd_7300581 416523012231311797440305 := by
  unfold tailWord_7300581
  simp only [CollatzResearch.WordTrace]
  refine ⟨266274064364249351813909597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177516042909499567875939731 266274064364249351813909597)
  ·
    refine ⟨99852774136593506930216099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266274064364249351813909597 99852774136593506930216099)
    ·
      refine ⟨149779161204890260395324149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99852774136593506930216099 149779161204890260395324149)
      ·
        refine ⟨14041796362958461912061639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149779161204890260395324149 14041796362958461912061639)
        ·
          refine ⟨21062694544437692868092459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14041796362958461912061639 21062694544437692868092459)
          ·
            refine ⟨31594041816656539302138689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21062694544437692868092459 31594041816656539302138689)
            ·
              refine ⟨23695531362492404476604017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31594041816656539302138689 23695531362492404476604017)
              ·
                refine ⟨17771648521869303357453013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23695531362492404476604017 17771648521869303357453013)
                ·
                  refine ⟨416523012231311797440305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17771648521869303357453013 416523012231311797440305)
                  ·
                    rfl

theorem cell23_7300581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_7300581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300581 prefixEnd_7300581 := by exact prefixLift 7300581
  have htrace : WordTrace (prefixWord ++ tailWord_7300581) baseStart_7300581 baseEnd_7300581 := by
    simpa [prefixWord, tailWord_7300581, baseEnd_7300581] using wordTrace_append hprefix tailTrace_7300581
  have hstable : (prefixWord ++ tailWord_7300581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300581).length < 2 ^ (prefixWord ++ tailWord_7300581).sum := by decide
  have hdescent : baseEnd_7300581 < baseStart_7300581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300601 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 7, 2]
def baseStart_7300601 : Nat := 118140960795 + 7300601 * 2 ^ 59
def prefixEnd_7300601 : Nat := 4983230072969 + 3 ^ 40 * 7300601 * 2
def baseEnd_7300601 : Nat := 3748717379694896098712653

theorem tailTrace_7300601 : CollatzResearch.WordTrace tailWord_7300601 prefixEnd_7300601 3748717379694896098712653 := by
  unfold tailWord_7300601
  simp only [CollatzResearch.WordTrace]
  refine ⟨266274793824176895229637657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177516529216117930153091771 266274793824176895229637657)
  ·
    refine ⟨199706095368132671422228243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266274793824176895229637657 199706095368132671422228243)
    ·
      refine ⟨299559143052199007133342365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199706095368132671422228243 299559143052199007133342365)
      ·
        refine ⟨112334678644574627675003387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299559143052199007133342365 112334678644574627675003387)
        ·
          refine ⟨168502017966861941512505081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112334678644574627675003387 168502017966861941512505081)
          ·
            refine ⟨126376513475146456134378811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168502017966861941512505081 126376513475146456134378811)
            ·
              refine ⟨189564770212719684201568217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126376513475146456134378811 189564770212719684201568217)
              ·
                refine ⟨142173577659539763151176163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189564770212719684201568217 142173577659539763151176163)
                ·
                  refine ⟨213260366489309644726764245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142173577659539763151176163 213260366489309644726764245)
                  ·
                    refine ⟨4998289839593194798283537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213260366489309644726764245 4998289839593194798283537)
                    ·
                      refine ⟨3748717379694896098712653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998289839593194798283537 3748717379694896098712653)
                      ·
                        rfl

theorem cell23_7300601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_7300601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300601 prefixEnd_7300601 := by exact prefixLift 7300601
  have htrace : WordTrace (prefixWord ++ tailWord_7300601) baseStart_7300601 baseEnd_7300601 := by
    simpa [prefixWord, tailWord_7300601, baseEnd_7300601] using wordTrace_append hprefix tailTrace_7300601
  have hstable : (prefixWord ++ tailWord_7300601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300601).length < 2 ^ (prefixWord ++ tailWord_7300601).sum := by decide
  have hdescent : baseEnd_7300601 < baseStart_7300601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300615 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 5]
def baseStart_7300615 : Nat := 118140960795 + 7300615 * 2 ^ 59
def prefixEnd_7300615 : Nat := 4983230072969 + 3 ^ 40 * 7300615 * 2
def baseEnd_7300615 : Nat := 416524952047117671548621

theorem tailTrace_7300615 : CollatzResearch.WordTrace tailWord_7300615 prefixEnd_7300615 416524952047117671548621 := by
  unfold tailWord_7300615
  simp only [CollatzResearch.WordTrace]
  refine ⟨266275304446126175620647299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177516869630750783747098199 266275304446126175620647299)
  ·
    refine ⟨399412956669189263430970949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266275304446126175620647299 399412956669189263430970949)
    ·
      refine ⟨74889929375472986893307053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399412956669189263430970949 74889929375472986893307053)
      ·
        refine ⟨28083723515802370084990145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74889929375472986893307053 28083723515802370084990145)
        ·
          refine ⟨21062792636851777563742609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28083723515802370084990145 21062792636851777563742609)
          ·
            refine ⟨15797094477638833172806957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21062792636851777563742609 15797094477638833172806957)
            ·
              refine ⟨5923910429114562439802609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15797094477638833172806957 5923910429114562439802609)
              ·
                refine ⟨4442932821835921829851957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923910429114562439802609 4442932821835921829851957)
                ·
                  refine ⟨416524952047117671548621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442932821835921829851957 416524952047117671548621)
                  ·
                    rfl

theorem cell23_7300615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 5].length) (baseStart_7300615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300615 prefixEnd_7300615 := by exact prefixLift 7300615
  have htrace : WordTrace (prefixWord ++ tailWord_7300615) baseStart_7300615 baseEnd_7300615 := by
    simpa [prefixWord, tailWord_7300615, baseEnd_7300615] using wordTrace_append hprefix tailTrace_7300615
  have hstable : (prefixWord ++ tailWord_7300615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300615).length < 2 ^ (prefixWord ++ tailWord_7300615).sum := by decide
  have hdescent : baseEnd_7300615 < baseStart_7300615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300671 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 6]
def baseStart_7300671 : Nat := 118140960795 + 7300671 * 2 ^ 59
def prefixEnd_7300671 : Nat := 4983230072969 + 3 ^ 40 * 7300671 * 2
def baseEnd_7300671 : Nat := 416528147037856758315259

theorem tailTrace_7300671 : CollatzResearch.WordTrace tailWord_7300671 prefixEnd_7300671 416528147037856758315259 := by
  unfold tailWord_7300671
  simp only [CollatzResearch.WordTrace]
  refine ⟨266277346933923297184685867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177518231289282198123123911 266277346933923297184685867)
  ·
    refine ⟨399416020400884945777028801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266277346933923297184685867 399416020400884945777028801)
    ·
      refine ⟨299562015300663709332771601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399416020400884945777028801 299562015300663709332771601)
      ·
        refine ⟨224671511475497781999578701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299562015300663709332771601 224671511475497781999578701)
        ·
          refine ⟨84251816803311668249842013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224671511475497781999578701 84251816803311668249842013)
          ·
            refine ⟨31594431301241875593690755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84251816803311668249842013 31594431301241875593690755)
            ·
              refine ⟨47391646951862813390536133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31594431301241875593690755 47391646951862813390536133)
              ·
                refine ⟨8885933803474277510725525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47391646951862813390536133 8885933803474277510725525)
                ·
                  refine ⟨416528147037856758315259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8885933803474277510725525 416528147037856758315259)
                  ·
                    rfl

theorem cell23_7300671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 6].length) (baseStart_7300671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300671 prefixEnd_7300671 := by exact prefixLift 7300671
  have htrace : WordTrace (prefixWord ++ tailWord_7300671) baseStart_7300671 baseEnd_7300671 := by
    simpa [prefixWord, tailWord_7300671, baseEnd_7300671] using wordTrace_append hprefix tailTrace_7300671
  have hstable : (prefixWord ++ tailWord_7300671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300671).length < 2 ^ (prefixWord ++ tailWord_7300671).sum := by decide
  have hdescent : baseEnd_7300671 < baseStart_7300671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300766 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_7300766 : Nat := 118140960795 + 7300766 * 2 ^ 59
def prefixEnd_7300766 : Nat := 4983230072969 + 3 ^ 40 * 7300766 * 2
def baseEnd_7300766 : Nat := 3748802104002887953149395

theorem tailTrace_7300766 : CollatzResearch.WordTrace tailWord_7300766 prefixEnd_7300766 3748802104002887953149395 := by
  unfold tailWord_7300766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285101483572391051174269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177520541245719418939596101 33285101483572391051174269)
  ·
    refine ⟨12481913056339646644190351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33285101483572391051174269 12481913056339646644190351)
    ·
      refine ⟨18722869584509469966285527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481913056339646644190351 18722869584509469966285527)
      ·
        refine ⟨28084304376764204949428291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18722869584509469966285527 28084304376764204949428291)
        ·
          refine ⟨42126456565146307424142437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28084304376764204949428291 42126456565146307424142437)
          ·
            refine ⟨7898710605964932642026707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42126456565146307424142437 7898710605964932642026707)
            ·
              refine ⟨11848065908947398963040061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898710605964932642026707 11848065908947398963040061)
              ·
                refine ⟨4443024715855274611140023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11848065908947398963040061 4443024715855274611140023)
                ·
                  refine ⟨6664537073782911916710035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443024715855274611140023 6664537073782911916710035)
                  ·
                    refine ⟨9996805610674367875065053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6664537073782911916710035 9996805610674367875065053)
                    ·
                      refine ⟨3748802104002887953149395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996805610674367875065053 3748802104002887953149395)
                      ·
                        rfl

theorem cell23_7300766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_7300766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300766 prefixEnd_7300766 := by exact prefixLift 7300766
  have htrace : WordTrace (prefixWord ++ tailWord_7300766) baseStart_7300766 baseEnd_7300766 := by
    simpa [prefixWord, tailWord_7300766, baseEnd_7300766] using wordTrace_append hprefix tailTrace_7300766
  have hstable : (prefixWord ++ tailWord_7300766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300766).length < 2 ^ (prefixWord ++ tailWord_7300766).sum := by decide
  have hdescent : baseEnd_7300766 < baseStart_7300766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300776 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7300776 : Nat := 118140960795 + 7300776 * 2 ^ 59
def prefixEnd_7300776 : Nat := 4983230072969 + 3 ^ 40 * 7300776 * 2
def baseEnd_7300776 : Nat := 3748807238809432914024349

theorem tailTrace_7300776 : CollatzResearch.WordTrace tailWord_7300776 prefixEnd_7300776 3748807238809432914024349 := by
  unfold tailWord_7300776
  simp only [CollatzResearch.WordTrace]
  refine ⟨133140588299271450058629091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177520784399028600078172121 133140588299271450058629091)
  ·
    refine ⟨199710882448907175087943637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133140588299271450058629091 199710882448907175087943637)
    ·
      refine ⟨4680723807396261916123679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 199710882448907175087943637 4680723807396261916123679)
      ·
        refine ⟨7021085711094392874185519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680723807396261916123679 7021085711094392874185519)
        ·
          refine ⟨10531628566641589311278279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021085711094392874185519 10531628566641589311278279)
          ·
            refine ⟨15797442849962383966917419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531628566641589311278279 15797442849962383966917419)
            ·
              refine ⟨23696164274943575950376129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15797442849962383966917419 23696164274943575950376129)
              ·
                refine ⟨17772123206207681962782097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23696164274943575950376129 17772123206207681962782097)
                ·
                  refine ⟨13329092404655761472086573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17772123206207681962782097 13329092404655761472086573)
                  ·
                    refine ⟨4998409651745910552032465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13329092404655761472086573 4998409651745910552032465)
                    ·
                      refine ⟨3748807238809432914024349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998409651745910552032465 3748807238809432914024349)
                      ·
                        rfl

theorem cell23_7300776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7300776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300776 prefixEnd_7300776 := by exact prefixLift 7300776
  have htrace : WordTrace (prefixWord ++ tailWord_7300776) baseStart_7300776 baseEnd_7300776 := by
    simpa [prefixWord, tailWord_7300776, baseEnd_7300776] using wordTrace_append hprefix tailTrace_7300776
  have hstable : (prefixWord ++ tailWord_7300776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300776).length < 2 ^ (prefixWord ++ tailWord_7300776).sum := by decide
  have hdescent : baseEnd_7300776 < baseStart_7300776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300805 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_7300805 : Nat := 118140960795 + 7300805 * 2 ^ 59
def prefixEnd_7300805 : Nat := 4983230072969 + 3 ^ 40 * 7300805 * 2
def baseEnd_7300805 : Nat := 3748822129748413300561715

theorem tailTrace_7300805 : CollatzResearch.WordTrace tailWord_7300805 prefixEnd_7300805 3748822129748413300561715 := by
  unfold tailWord_7300805
  simp only [CollatzResearch.WordTrace]
  refine ⟨266282234315437838070063869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177521489543625225380042579 266282234315437838070063869)
  ·
    refine ⟨99855837868289189276273951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266282234315437838070063869 99855837868289189276273951)
    ·
      refine ⟨149783756802433783914410927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99855837868289189276273951 149783756802433783914410927)
      ·
        refine ⟨224675635203650675871616391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149783756802433783914410927 224675635203650675871616391)
        ·
          refine ⟨337013452805476013807424587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224675635203650675871616391 337013452805476013807424587)
          ·
            refine ⟨505520179208214020711136881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337013452805476013807424587 505520179208214020711136881)
            ·
              refine ⟨379140134406160515533352661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505520179208214020711136881 379140134406160515533352661)
              ·
                refine ⟨8886096900144387082812953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 379140134406160515533352661 8886096900144387082812953)
                ·
                  refine ⟨6664572675108290312109715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8886096900144387082812953 6664572675108290312109715)
                  ·
                    refine ⟨9996859012662435468164573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6664572675108290312109715 9996859012662435468164573)
                    ·
                      refine ⟨3748822129748413300561715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996859012662435468164573 3748822129748413300561715)
                      ·
                        rfl

theorem cell23_7300805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_7300805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300805 prefixEnd_7300805 := by exact prefixLift 7300805
  have htrace : WordTrace (prefixWord ++ tailWord_7300805) baseStart_7300805 baseEnd_7300805 := by
    simpa [prefixWord, tailWord_7300805, baseEnd_7300805] using wordTrace_append hprefix tailTrace_7300805
  have hstable : (prefixWord ++ tailWord_7300805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300805).length < 2 ^ (prefixWord ++ tailWord_7300805).sum := by decide
  have hdescent : baseEnd_7300805 < baseStart_7300805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300806 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7300806 : Nat := 118140960795 + 7300806 * 2 ^ 59
def prefixEnd_7300806 : Nat := 4983230072969 + 3 ^ 40 * 7300806 * 2
def baseEnd_7300806 : Nat := 3748822643229067796649211

theorem tailTrace_7300806 : CollatzResearch.WordTrace tailWord_7300806 prefixEnd_7300806 3748822643229067796649211 := by
  unfold tailWord_7300806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321320962138569226276571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177521513858956143493900181 8321320962138569226276571)
  ·
    refine ⟨12481981443207853839414857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8321320962138569226276571 12481981443207853839414857)
    ·
      refine ⟨9361486082405890379561143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12481981443207853839414857 9361486082405890379561143)
      ·
        refine ⟨14042229123608835569341715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361486082405890379561143 14042229123608835569341715)
        ·
          refine ⟨21063343685413253354012573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14042229123608835569341715 21063343685413253354012573)
          ·
            refine ⟨7898753882029970007754715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21063343685413253354012573 7898753882029970007754715)
            ·
              refine ⟨11848130823044955011632073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898753882029970007754715 11848130823044955011632073)
              ·
                refine ⟨8886098117283716258724055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11848130823044955011632073 8886098117283716258724055)
                ·
                  refine ⟨13329147175925574388086083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8886098117283716258724055 13329147175925574388086083)
                  ·
                    refine ⟨19993720763888361582129125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13329147175925574388086083 19993720763888361582129125)
                    ·
                      refine ⟨3748822643229067796649211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19993720763888361582129125 3748822643229067796649211)
                      ·
                        rfl

theorem cell23_7300806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7300806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300806 prefixEnd_7300806 := by exact prefixLift 7300806
  have htrace : WordTrace (prefixWord ++ tailWord_7300806) baseStart_7300806 baseEnd_7300806 := by
    simpa [prefixWord, tailWord_7300806, baseEnd_7300806] using wordTrace_append hprefix tailTrace_7300806
  have hstable : (prefixWord ++ tailWord_7300806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300806).length < 2 ^ (prefixWord ++ tailWord_7300806).sum := by decide
  have hdescent : baseEnd_7300806 < baseStart_7300806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300841 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_7300841 : Nat := 118140960795 + 7300841 * 2 ^ 59
def prefixEnd_7300841 : Nat := 4983230072969 + 3 ^ 40 * 7300841 * 2
def baseEnd_7300841 : Nat := 3748840615051975159711549

theorem tailTrace_7300841 : CollatzResearch.WordTrace tailWord_7300841 prefixEnd_7300841 3748840615051975159711549 := by
  unfold tailWord_7300841
  simp only [CollatzResearch.WordTrace]
  refine ⟨266283547343307416218374377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177522364895538277478916251 266283547343307416218374377)
  ·
    refine ⟨199712660507480562163780783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266283547343307416218374377 199712660507480562163780783)
    ·
      refine ⟨299568990761220843245671175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199712660507480562163780783 299568990761220843245671175)
      ·
        refine ⟨449353486141831264868506763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299568990761220843245671175 449353486141831264868506763)
        ·
          refine ⟨674030229212746897302760145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449353486141831264868506763 674030229212746897302760145)
          ·
            refine ⟨505522671909560172977070109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674030229212746897302760145 505522671909560172977070109)
            ·
              refine ⟨189571001966085064866401291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505522671909560172977070109 189571001966085064866401291)
              ·
                refine ⟨284356502949127597299601937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189571001966085064866401291 284356502949127597299601937)
                ·
                  refine ⟨213267377211845697974701453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284356502949127597299601937 213267377211845697974701453)
                  ·
                    refine ⟨79975266454442136740513045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213267377211845697974701453 79975266454442136740513045)
                    ·
                      refine ⟨3748840615051975159711549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79975266454442136740513045 3748840615051975159711549)
                      ·
                        rfl

theorem cell23_7300841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_7300841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300841 prefixEnd_7300841 := by exact prefixLift 7300841
  have htrace : WordTrace (prefixWord ++ tailWord_7300841) baseStart_7300841 baseEnd_7300841 := by
    simpa [prefixWord, tailWord_7300841, baseEnd_7300841] using wordTrace_append hprefix tailTrace_7300841
  have hstable : (prefixWord ++ tailWord_7300841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300841).length < 2 ^ (prefixWord ++ tailWord_7300841).sum := by decide
  have hdescent : baseEnd_7300841 < baseStart_7300841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300868 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 9]
def baseStart_7300868 : Nat := 118140960795 + 7300868 * 2 ^ 59
def prefixEnd_7300868 : Nat := 4983230072969 + 3 ^ 40 * 7300868 * 2
def baseEnd_7300868 : Nat := 416539386558849617119325

theorem tailTrace_7300868 : CollatzResearch.WordTrace tailWord_7300868 prefixEnd_7300868 416539386558849617119325 := by
  unfold tailWord_7300868
  simp only [CollatzResearch.WordTrace]
  refine ⟨133142266057104799914803629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177523021409473066553071505 133142266057104799914803629)
  ·
    refine ⟨49928349771414299968051361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133142266057104799914803629 49928349771414299968051361)
    ·
      refine ⟨37446262328560724976038521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49928349771414299968051361 37446262328560724976038521)
      ·
        refine ⟨28084696746420543732028891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37446262328560724976038521 28084696746420543732028891)
        ·
          refine ⟨42127045119630815598043337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28084696746420543732028891 42127045119630815598043337)
          ·
            refine ⟨31595283839723111698532503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42127045119630815598043337 31595283839723111698532503)
            ·
              refine ⟨47392925759584667547798755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31595283839723111698532503 47392925759584667547798755)
              ·
                refine ⟨71089388639377001321698133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47392925759584667547798755 71089388639377001321698133)
                ·
                  refine ⟨416539386558849617119325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71089388639377001321698133 416539386558849617119325)
                  ·
                    rfl

theorem cell23_7300868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_7300868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300868 prefixEnd_7300868 := by exact prefixLift 7300868
  have htrace : WordTrace (prefixWord ++ tailWord_7300868) baseStart_7300868 baseEnd_7300868 := by
    simpa [prefixWord, tailWord_7300868, baseEnd_7300868] using wordTrace_append hprefix tailTrace_7300868
  have hstable : (prefixWord ++ tailWord_7300868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300868).length < 2 ^ (prefixWord ++ tailWord_7300868).sum := by decide
  have hdescent : baseEnd_7300868 < baseStart_7300868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300877 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7300877 : Nat := 118140960795 + 7300877 * 2 ^ 59
def prefixEnd_7300877 : Nat := 4983230072969 + 3 ^ 40 * 7300877 * 2
def baseEnd_7300877 : Nat := 3748859100355537018861385

theorem tailTrace_7300877 : CollatzResearch.WordTrace tailWord_7300877 prefixEnd_7300877 3748859100355537018861385 := by
  unfold tailWord_7300877
  simp only [CollatzResearch.WordTrace]
  refine ⟨266284860371176994366684885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177523240247451329577789923 266284860371176994366684885)
  ·
    refine ⟨6241051414949460805469177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 266284860371176994366684885 6241051414949460805469177)
    ·
      refine ⟨4680788561212095604101883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6241051414949460805469177 4680788561212095604101883)
      ·
        refine ⟨7021182841818143406152825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680788561212095604101883 7021182841818143406152825)
        ·
          refine ⟨5265887131363607554614619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7021182841818143406152825 5265887131363607554614619)
          ·
            refine ⟨7898830697045411331921929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265887131363607554614619 7898830697045411331921929)
            ·
              refine ⟨5924123022784058498941447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7898830697045411331921929 5924123022784058498941447)
              ·
                refine ⟨8886184534176087748412171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924123022784058498941447 8886184534176087748412171)
                ·
                  refine ⟨13329276801264131622618257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8886184534176087748412171 13329276801264131622618257)
                  ·
                    refine ⟨9996957600948098716963693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13329276801264131622618257 9996957600948098716963693)
                    ·
                      refine ⟨3748859100355537018861385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9996957600948098716963693 3748859100355537018861385)
                      ·
                        rfl

theorem cell23_7300877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7300877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300877 prefixEnd_7300877 := by exact prefixLift 7300877
  have htrace : WordTrace (prefixWord ++ tailWord_7300877) baseStart_7300877 baseEnd_7300877 := by
    simpa [prefixWord, tailWord_7300877, baseEnd_7300877] using wordTrace_append hprefix tailTrace_7300877
  have hstable : (prefixWord ++ tailWord_7300877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300877).length < 2 ^ (prefixWord ++ tailWord_7300877).sum := by decide
  have hdescent : baseEnd_7300877 < baseStart_7300877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300885 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 5]
def baseStart_7300885 : Nat := 118140960795 + 7300885 * 2 ^ 59
def prefixEnd_7300885 : Nat := 4983230072969 + 3 ^ 40 * 7300885 * 2
def baseEnd_7300885 : Nat := 416540356466752554173483

theorem tailTrace_7300885 : CollatzResearch.WordTrace tailWord_7300885 prefixEnd_7300885 416540356466752554173483 := by
  unfold tailWord_7300885
  simp only [CollatzResearch.WordTrace]
  refine ⟨266285152155148011732976109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177523434770098674488650739 266285152155148011732976109)
  ·
    refine ⟨99856932058180504399866041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266285152155148011732976109 99856932058180504399866041)
    ·
      refine ⟨74892699043635378299899531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99856932058180504399866041 74892699043635378299899531)
      ·
        refine ⟨112339048565453067449849297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74892699043635378299899531 112339048565453067449849297)
        ·
          refine ⟨84254286424089800587386973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112339048565453067449849297 84254286424089800587386973)
          ·
            refine ⟨31595357409033675220270115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84254286424089800587386973 31595357409033675220270115)
            ·
              refine ⟨47393036113550512830405173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31595357409033675220270115 47393036113550512830405173)
              ·
                refine ⟨4443097135645360577850485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47393036113550512830405173 4443097135645360577850485)
                ·
                  refine ⟨416540356466752554173483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4443097135645360577850485 416540356466752554173483)
                  ·
                    rfl

theorem cell23_7300885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_7300885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300885 prefixEnd_7300885 := by exact prefixLift 7300885
  have htrace : WordTrace (prefixWord ++ tailWord_7300885) baseStart_7300885 baseEnd_7300885 := by
    simpa [prefixWord, tailWord_7300885, baseEnd_7300885] using wordTrace_append hprefix tailTrace_7300885
  have hstable : (prefixWord ++ tailWord_7300885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300885).length < 2 ^ (prefixWord ++ tailWord_7300885).sum := by decide
  have hdescent : baseEnd_7300885 < baseStart_7300885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7300935 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_7300935 : Nat := 118140960795 + 7300935 * 2 ^ 59
def prefixEnd_7300935 : Nat := 4983230072969 + 3 ^ 40 * 7300935 * 2
def baseEnd_7300935 : Nat := 3748888882233497791936117

theorem tailTrace_7300935 : CollatzResearch.WordTrace tailWord_7300935 prefixEnd_7300935 3748888882233497791936117 := by
  unfold tailWord_7300935
  simp only [CollatzResearch.WordTrace]
  refine ⟨266286975804966870272296259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177524650536644580181530839 266286975804966870272296259)
  ·
    refine ⟨399430463707450305408444389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266286975804966870272296259 399430463707450305408444389)
    ·
      refine ⟨74893211945146932264083323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399430463707450305408444389 74893211945146932264083323)
      ·
        refine ⟨112339817917720398396124985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74893211945146932264083323 112339817917720398396124985)
        ·
          refine ⟨84254863438290298797093739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112339817917720398396124985 84254863438290298797093739)
          ·
            refine ⟨126382295157435448195640609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84254863438290298797093739 126382295157435448195640609)
            ·
              refine ⟨94786721368076586146730457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126382295157435448195640609 94786721368076586146730457)
              ·
                refine ⟨71090041026057439610047843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94786721368076586146730457 71090041026057439610047843)
                ·
                  refine ⟨106635061539086159415071765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71090041026057439610047843 106635061539086159415071765)
                  ·
                    refine ⟨4998518509644663722581489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106635061539086159415071765 4998518509644663722581489)
                    ·
                      refine ⟨3748888882233497791936117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998518509644663722581489 3748888882233497791936117)
                      ·
                        rfl

theorem cell23_7300935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_7300935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7300935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7300935 prefixEnd_7300935 := by exact prefixLift 7300935
  have htrace : WordTrace (prefixWord ++ tailWord_7300935) baseStart_7300935 baseEnd_7300935 := by
    simpa [prefixWord, tailWord_7300935, baseEnd_7300935] using wordTrace_append hprefix tailTrace_7300935
  have hstable : (prefixWord ++ tailWord_7300935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7300935).length < 2 ^ (prefixWord ++ tailWord_7300935).sum := by decide
  have hdescent : baseEnd_7300935 < baseStart_7300935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7300935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301055 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_7301055 : Nat := 118140960795 + 7301055 * 2 ^ 59
def prefixEnd_7301055 : Nat := 4983230072969 + 3 ^ 40 * 7301055 * 2
def baseEnd_7301055 : Nat := 3748950499912037322435565

theorem tailTrace_7301055 : CollatzResearch.WordTrace tailWord_7301055 prefixEnd_7301055 3748950499912037322435565 := by
  unfold tailWord_7301055
  simp only [CollatzResearch.WordTrace]
  refine ⟨266291352564532130766664619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177527568376354753844443079 266291352564532130766664619)
  ·
    refine ⟨399437028846798196149996929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266291352564532130766664619 399437028846798196149996929)
    ·
      refine ⟨299577771635098647112497697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399437028846798196149996929 299577771635098647112497697)
      ·
        refine ⟨224683328726323985334373273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299577771635098647112497697 224683328726323985334373273)
        ·
          refine ⟨168512496544742989000779955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224683328726323985334373273 168512496544742989000779955)
          ·
            refine ⟨252768744817114483501169933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168512496544742989000779955 252768744817114483501169933)
            ·
              refine ⟨94788279306417931312938725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252768744817114483501169933 94788279306417931312938725)
              ·
                refine ⟨17772802369953362121176011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94788279306417931312938725 17772802369953362121176011)
                ·
                  refine ⟨26659203554930043181764017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17772802369953362121176011 26659203554930043181764017)
                  ·
                    refine ⟨19994402666197532386323013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26659203554930043181764017 19994402666197532386323013)
                    ·
                      refine ⟨3748950499912037322435565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19994402666197532386323013 3748950499912037322435565)
                      ·
                        rfl

theorem cell23_7301055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_7301055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301055 prefixEnd_7301055 := by exact prefixLift 7301055
  have htrace : WordTrace (prefixWord ++ tailWord_7301055) baseStart_7301055 baseEnd_7301055 := by
    simpa [prefixWord, tailWord_7301055, baseEnd_7301055] using wordTrace_append hprefix tailTrace_7301055
  have hstable : (prefixWord ++ tailWord_7301055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301055).length < 2 ^ (prefixWord ++ tailWord_7301055).sum := by decide
  have hdescent : baseEnd_7301055 < baseStart_7301055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301076 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7301076 : Nat := 118140960795 + 7301076 * 2 ^ 59
def prefixEnd_7301076 : Nat := 4983230072969 + 3 ^ 40 * 7301076 * 2
def baseEnd_7301076 : Nat := 3748961283005781740272969

theorem tailTrace_7301076 : CollatzResearch.WordTrace tailWord_7301076 prefixEnd_7301076 3748961283005781740272969 := by
  unfold tailWord_7301076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133146059248728025676589541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177528078998304034235452721 133146059248728025676589541)
  ·
    refine ⟨24964886109136504814360539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133146059248728025676589541 24964886109136504814360539)
    ·
      refine ⟨37447329163704757221540809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24964886109136504814360539 37447329163704757221540809)
      ·
        refine ⟨28085496872778567916155607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37447329163704757221540809 28085496872778567916155607)
        ·
          refine ⟨42128245309167851874233411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28085496872778567916155607 42128245309167851874233411)
          ·
            refine ⟨63192367963751777811350117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42128245309167851874233411 63192367963751777811350117)
            ·
              refine ⟨11848568993203458339628147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63192367963751777811350117 11848568993203458339628147)
              ·
                refine ⟨17772853489805187509442221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848568993203458339628147 17772853489805187509442221)
                ·
                  refine ⟨6664820058676945316040833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17772853489805187509442221 6664820058676945316040833)
                  ·
                    refine ⟨4998615044007708987030625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6664820058676945316040833 4998615044007708987030625)
                    ·
                      refine ⟨3748961283005781740272969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998615044007708987030625 3748961283005781740272969)
                      ·
                        rfl

theorem cell23_7301076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7301076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301076 prefixEnd_7301076 := by exact prefixLift 7301076
  have htrace : WordTrace (prefixWord ++ tailWord_7301076) baseStart_7301076 baseEnd_7301076 := by
    simpa [prefixWord, tailWord_7301076, baseEnd_7301076] using wordTrace_append hprefix tailTrace_7301076
  have hstable : (prefixWord ++ tailWord_7301076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301076).length < 2 ^ (prefixWord ++ tailWord_7301076).sum := by decide
  have hdescent : baseEnd_7301076 < baseStart_7301076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301145 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_7301145 : Nat := 118140960795 + 7301145 * 2 ^ 59
def prefixEnd_7301145 : Nat := 4983230072969 + 3 ^ 40 * 7301145 * 2
def baseEnd_7301145 : Nat := 3748996713170941970310151

theorem tailTrace_7301145 : CollatzResearch.WordTrace tailWord_7301145 prefixEnd_7301145 3748996713170941970310151 := by
  unfold tailWord_7301145
  simp only [CollatzResearch.WordTrace]
  refine ⟨266294635134206076137440889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177529756756137384091627259 266294635134206076137440889)
  ·
    refine ⟨199720976350654557103080667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266294635134206076137440889 199720976350654557103080667)
    ·
      refine ⟨299581464525981835654621001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199720976350654557103080667 299581464525981835654621001)
      ·
        refine ⟨224686098394486376740965751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299581464525981835654621001 224686098394486376740965751)
        ·
          refine ⟨337029147591729565111448627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224686098394486376740965751 337029147591729565111448627)
          ·
            refine ⟨505543721387594347667172941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337029147591729565111448627 505543721387594347667172941)
            ·
              refine ⟨189578895520347880375189853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505543721387594347667172941 189578895520347880375189853)
              ·
                refine ⟨71092085820130455140696195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189578895520347880375189853 71092085820130455140696195)
                ·
                  refine ⟨106638128730195682711044293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71092085820130455140696195 106638128730195682711044293)
                  ·
                    refine ⟨19994649136911690508320805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106638128730195682711044293 19994649136911690508320805)
                    ·
                      refine ⟨3748996713170941970310151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19994649136911690508320805 3748996713170941970310151)
                      ·
                        rfl

theorem cell23_7301145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_7301145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301145 prefixEnd_7301145 := by exact prefixLift 7301145
  have htrace : WordTrace (prefixWord ++ tailWord_7301145) baseStart_7301145 baseEnd_7301145 := by
    simpa [prefixWord, tailWord_7301145, baseEnd_7301145] using wordTrace_append hprefix tailTrace_7301145
  have hstable : (prefixWord ++ tailWord_7301145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301145).length < 2 ^ (prefixWord ++ tailWord_7301145).sum := by decide
  have hdescent : baseEnd_7301145 < baseStart_7301145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301153 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_7301153 : Nat := 118140960795 + 7301153 * 2 ^ 59
def prefixEnd_7301153 : Nat := 4983230072969 + 3 ^ 40 * 7301153 * 2
def baseEnd_7301153 : Nat := 3749000821016177939010115

theorem tailTrace_7301153 : CollatzResearch.WordTrace tailWord_7301153 prefixEnd_7301153 3749000821016177939010115 := by
  unfold tailWord_7301153
  simp only [CollatzResearch.WordTrace]
  refine ⟨266294926918177093503732113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177529951278784729002488075 266294926918177093503732113)
  ·
    refine ⟨199721195188632820127799085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266294926918177093503732113 199721195188632820127799085)
    ·
      refine ⟨74895448195737307547924657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199721195188632820127799085 74895448195737307547924657)
      ·
        refine ⟨56171586146802980660943493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74895448195737307547924657 56171586146802980660943493)
        ·
          refine ⟨10532172402525558873926905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56171586146802980660943493 10532172402525558873926905)
          ·
            refine ⟨7899129301894169155445179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532172402525558873926905 7899129301894169155445179)
            ·
              refine ⟨11848693952841253733167769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899129301894169155445179 11848693952841253733167769)
              ·
                refine ⟨8886520464630940299875827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11848693952841253733167769 8886520464630940299875827)
                ·
                  refine ⟨13329780696946410449813741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8886520464630940299875827 13329780696946410449813741)
                  ·
                    refine ⟨4998667761354903918680153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13329780696946410449813741 4998667761354903918680153)
                    ·
                      refine ⟨3749000821016177939010115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998667761354903918680153 3749000821016177939010115)
                      ·
                        rfl

theorem cell23_7301153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_7301153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301153 prefixEnd_7301153 := by exact prefixLift 7301153
  have htrace : WordTrace (prefixWord ++ tailWord_7301153) baseStart_7301153 baseEnd_7301153 := by
    simpa [prefixWord, tailWord_7301153, baseEnd_7301153] using wordTrace_append hprefix tailTrace_7301153
  have hstable : (prefixWord ++ tailWord_7301153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301153).length < 2 ^ (prefixWord ++ tailWord_7301153).sum := by decide
  have hdescent : baseEnd_7301153 < baseStart_7301153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301155 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 9]
def baseStart_7301155 : Nat := 118140960795 + 7301155 * 2 ^ 59
def prefixEnd_7301155 : Nat := 4983230072969 + 3 ^ 40 * 7301155 * 2
def baseEnd_7301155 : Nat := 416555760886387436798345

theorem tailTrace_7301155 : CollatzResearch.WordTrace tailWord_7301155 prefixEnd_7301155 416555760886387436798345 := by
  unfold tailWord_7301155
  simp only [CollatzResearch.WordTrace]
  refine ⟨266294999864169847845304919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177529999909446565230203279 266294999864169847845304919)
  ·
    refine ⟨399442499796254771767957379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266294999864169847845304919 399442499796254771767957379)
    ·
      refine ⟨599163749694382157651936069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399442499796254771767957379 599163749694382157651936069)
      ·
        refine ⟨112343203067696654559738013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599163749694382157651936069 112343203067696654559738013)
        ·
          refine ⟨42128701150386245459901755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112343203067696654559738013 42128701150386245459901755)
          ·
            refine ⟨63193051725579368189852633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42128701150386245459901755 63193051725579368189852633)
            ·
              refine ⟨47394788794184526142389475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63193051725579368189852633 47394788794184526142389475)
              ·
                refine ⟨71092183191276789213584213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47394788794184526142389475 71092183191276789213584213)
                ·
                  refine ⟨416555760886387436798345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71092183191276789213584213 416555760886387436798345)
                  ·
                    rfl

theorem cell23_7301155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 9].length) (baseStart_7301155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301155 prefixEnd_7301155 := by exact prefixLift 7301155
  have htrace : WordTrace (prefixWord ++ tailWord_7301155) baseStart_7301155 baseEnd_7301155 := by
    simpa [prefixWord, tailWord_7301155, baseEnd_7301155] using wordTrace_append hprefix tailTrace_7301155
  have hstable : (prefixWord ++ tailWord_7301155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301155).length < 2 ^ (prefixWord ++ tailWord_7301155).sum := by decide
  have hdescent : baseEnd_7301155 < baseStart_7301155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301166 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7301166 : Nat := 118140960795 + 7301166 * 2 ^ 59
def prefixEnd_7301166 : Nat := 4983230072969 + 3 ^ 40 * 7301166 * 2
def baseEnd_7301166 : Nat := 3749007496264686388147555

theorem tailTrace_7301166 : CollatzResearch.WordTrace tailWord_7301166 prefixEnd_7301166 3749007496264686388147555 := by
  unfold tailWord_7301166
  simp only [CollatzResearch.WordTrace]
  refine ⟨33286925133391249590494419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177530267378086664482636901 33286925133391249590494419)
  ·
    refine ⟨49930387700086874385741629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33286925133391249590494419 49930387700086874385741629)
    ·
      refine ⟨18723895387532577894653111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49930387700086874385741629 18723895387532577894653111)
      ·
        refine ⟨28085843081298866841979667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18723895387532577894653111 28085843081298866841979667)
        ·
          refine ⟨42128764621948300262969501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28085843081298866841979667 42128764621948300262969501)
          ·
            refine ⟨15798286733230612598613563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42128764621948300262969501 15798286733230612598613563)
            ·
              refine ⟨23697430099845918897920345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798286733230612598613563 23697430099845918897920345)
              ·
                refine ⟨17773072574884439173440259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23697430099845918897920345 17773072574884439173440259)
                ·
                  refine ⟨26659608862326658760160389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17773072574884439173440259 26659608862326658760160389)
                  ·
                    refine ⟨4998676661686248517530073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26659608862326658760160389 4998676661686248517530073)
                    ·
                      refine ⟨3749007496264686388147555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998676661686248517530073 3749007496264686388147555)
                      ·
                        rfl

theorem cell23_7301166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7301166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301166 prefixEnd_7301166 := by exact prefixLift 7301166
  have htrace : WordTrace (prefixWord ++ tailWord_7301166) baseStart_7301166 baseEnd_7301166 := by
    simpa [prefixWord, tailWord_7301166, baseEnd_7301166] using wordTrace_append hprefix tailTrace_7301166
  have hstable : (prefixWord ++ tailWord_7301166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301166).length < 2 ^ (prefixWord ++ tailWord_7301166).sum := by decide
  have hdescent : baseEnd_7301166 < baseStart_7301166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301206 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_7301206 : Nat := 118140960795 + 7301206 * 2 ^ 59
def prefixEnd_7301206 : Nat := 4983230072969 + 3 ^ 40 * 7301206 * 2
def baseEnd_7301206 : Nat := 416558670610096247960819

theorem tailTrace_7301206 : CollatzResearch.WordTrace tailWord_7301206 prefixEnd_7301206 416558670610096247960819 := by
  unfold tailWord_7301206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643553749186567722213217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177531239991323389036940981 16643553749186567722213217)
  ·
    refine ⟨12482665311889925791659913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16643553749186567722213217 12482665311889925791659913)
    ·
      refine ⟨9361998983917444343744935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12482665311889925791659913 9361998983917444343744935)
      ·
        refine ⟨14042998475876166515617403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361998983917444343744935 14042998475876166515617403)
        ·
          refine ⟨21064497713814249773426105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14042998475876166515617403 21064497713814249773426105)
          ·
            refine ⟨15798373285360687330069579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21064497713814249773426105 15798373285360687330069579)
            ·
              refine ⟨23697559928041030995104369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798373285360687330069579 23697559928041030995104369)
              ·
                refine ⟨17773169946030773246328277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23697559928041030995104369 17773169946030773246328277)
                ·
                  refine ⟨416558670610096247960819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17773169946030773246328277 416558670610096247960819)
                  ·
                    rfl

theorem cell23_7301206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_7301206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301206 prefixEnd_7301206 := by exact prefixLift 7301206
  have htrace : WordTrace (prefixWord ++ tailWord_7301206) baseStart_7301206 baseEnd_7301206 := by
    simpa [prefixWord, tailWord_7301206, baseEnd_7301206] using wordTrace_append hprefix tailTrace_7301206
  have hstable : (prefixWord ++ tailWord_7301206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301206).length < 2 ^ (prefixWord ++ tailWord_7301206).sum := by decide
  have hdescent : baseEnd_7301206 < baseStart_7301206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301215 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 10]
def baseStart_7301215 : Nat := 118140960795 + 7301215 * 2 ^ 59
def prefixEnd_7301215 : Nat := 4983230072969 + 3 ^ 40 * 7301215 * 2
def baseEnd_7301215 : Nat := 1249677552272252232144943

theorem tailTrace_7301215 : CollatzResearch.WordTrace tailWord_7301215 prefixEnd_7301215 1249677552272252232144943 := by
  unfold tailWord_7301215
  simp only [CollatzResearch.WordTrace]
  refine ⟨266297188243952478092489099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177531458829301652061659399 266297188243952478092489099)
  ·
    refine ⟨399445782365928717138733649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266297188243952478092489099 399445782365928717138733649)
    ·
      refine ⟨299584336774446537854050237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399445782365928717138733649 299584336774446537854050237)
      ·
        refine ⟨112344126290417451695268839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299584336774446537854050237 112344126290417451695268839)
        ·
          refine ⟨168516189435626177542903259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112344126290417451695268839 168516189435626177542903259)
          ·
            refine ⟨252774284153439266314354889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168516189435626177542903259 252774284153439266314354889)
            ·
              refine ⟨189580713115079449735766167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252774284153439266314354889 189580713115079449735766167)
              ·
                refine ⟨284371069672619174603649251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189580713115079449735766167 284371069672619174603649251)
                ·
                  refine ⟨426556604508928761905473877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284371069672619174603649251 426556604508928761905473877)
                  ·
                    refine ⟨1249677552272252232144943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 426556604508928761905473877 1249677552272252232144943)
                    ·
                      rfl

theorem cell23_7301215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_7301215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301215 prefixEnd_7301215 := by exact prefixLift 7301215
  have htrace : WordTrace (prefixWord ++ tailWord_7301215) baseStart_7301215 baseEnd_7301215 := by
    simpa [prefixWord, tailWord_7301215, baseEnd_7301215] using wordTrace_append hprefix tailTrace_7301215
  have hstable : (prefixWord ++ tailWord_7301215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301215).length < 2 ^ (prefixWord ++ tailWord_7301215).sum := by decide
  have hdescent : baseEnd_7301215 < baseStart_7301215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301239 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_7301239 : Nat := 118140960795 + 7301239 * 2 ^ 59
def prefixEnd_7301239 : Nat := 4983230072969 + 3 ^ 40 * 7301239 * 2
def baseEnd_7301239 : Nat := 3749044980352464602534719

theorem tailTrace_7301239 : CollatzResearch.WordTrace tailWord_7301239 prefixEnd_7301239 3749044980352464602534719 := by
  unfold tailWord_7301239
  simp only [CollatzResearch.WordTrace]
  refine ⟨266298063595865530191362771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177532042397243686794241847 266298063595865530191362771)
  ·
    refine ⟨399447095393798295287044157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266298063595865530191362771 399447095393798295287044157)
    ·
      refine ⟨149792660772674360732641559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399447095393798295287044157 149792660772674360732641559)
      ·
        refine ⟨224688991159011541098962339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149792660772674360732641559 224688991159011541098962339)
        ·
          refine ⟨337033486738517311648443509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224688991159011541098962339 337033486738517311648443509)
          ·
            refine ⟨31596889381735997967041579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337033486738517311648443509 31596889381735997967041579)
            ·
              refine ⟨47395334072603996950562369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31596889381735997967041579 47395334072603996950562369)
              ·
                refine ⟨35546500554452997712921777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47395334072603996950562369 35546500554452997712921777)
                ·
                  refine ⟨26659875415839748284691333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35546500554452997712921777 26659875415839748284691333)
                  ·
                    refine ⟨4998726640469952803379625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26659875415839748284691333 4998726640469952803379625)
                    ·
                      refine ⟨3749044980352464602534719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998726640469952803379625 3749044980352464602534719)
                      ·
                        rfl

theorem cell23_7301239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_7301239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301239 prefixEnd_7301239 := by exact prefixLift 7301239
  have htrace : WordTrace (prefixWord ++ tailWord_7301239) baseStart_7301239 baseEnd_7301239 := by
    simpa [prefixWord, tailWord_7301239, baseEnd_7301239] using wordTrace_append hprefix tailTrace_7301239
  have hstable : (prefixWord ++ tailWord_7301239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301239).length < 2 ^ (prefixWord ++ tailWord_7301239).sum := by decide
  have hdescent : baseEnd_7301239 < baseStart_7301239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301252 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7301252 : Nat := 118140960795 + 7301252 * 2 ^ 59
def prefixEnd_7301252 : Nat := 4983230072969 + 3 ^ 40 * 7301252 * 2
def baseEnd_7301252 : Nat := 3749051655600973051672159

theorem tailTrace_7301252 : CollatzResearch.WordTrace tailWord_7301252 prefixEnd_7301252 3749051655600973051672159 := by
  unfold tailWord_7301252
  simp only [CollatzResearch.WordTrace]
  refine ⟨133149268872409216705793005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177532358496545622274390673 133149268872409216705793005)
  ·
    refine ⟨49930975827153456264672377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133149268872409216705793005 49930975827153456264672377)
    ·
      refine ⟨37448231870365092198504283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49930975827153456264672377 37448231870365092198504283)
      ·
        refine ⟨56172347805547638297756425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448231870365092198504283 56172347805547638297756425)
        ·
          refine ⟨42129260854160728723317319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56172347805547638297756425 42129260854160728723317319)
          ·
            refine ⟨63193891281241093084975979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42129260854160728723317319 63193891281241093084975979)
            ·
              refine ⟨94790836921861639627463969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63193891281241093084975979 94790836921861639627463969)
              ·
                refine ⟨71093127691396229720597977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94790836921861639627463969 71093127691396229720597977)
                ·
                  refine ⟨53319845768547172290448483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71093127691396229720597977 53319845768547172290448483)
                  ·
                    refine ⟨79979768652820758435672725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53319845768547172290448483 79979768652820758435672725)
                    ·
                      refine ⟨3749051655600973051672159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79979768652820758435672725 3749051655600973051672159)
                      ·
                        rfl

theorem cell23_7301252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7301252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301252 prefixEnd_7301252 := by exact prefixLift 7301252
  have htrace : WordTrace (prefixWord ++ tailWord_7301252) baseStart_7301252 baseEnd_7301252 := by
    simpa [prefixWord, tailWord_7301252, baseEnd_7301252] using wordTrace_append hprefix tailTrace_7301252
  have hstable : (prefixWord ++ tailWord_7301252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301252).length < 2 ^ (prefixWord ++ tailWord_7301252).sum := by decide
  have hdescent : baseEnd_7301252 < baseStart_7301252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301256 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7301256 : Nat := 118140960795 + 7301256 * 2 ^ 59
def prefixEnd_7301256 : Nat := 4983230072969 + 3 ^ 40 * 7301256 * 2
def baseEnd_7301256 : Nat := 3749053709523591036022141

theorem tailTrace_7301256 : CollatzResearch.WordTrace tailWord_7301256 prefixEnd_7301256 3749053709523591036022141 := by
  unfold tailWord_7301256
  simp only [CollatzResearch.WordTrace]
  refine ⟨133149341818401971047365811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177532455757869294729821081 133149341818401971047365811)
  ·
    refine ⟨199724012727602956571048717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133149341818401971047365811 199724012727602956571048717)
    ·
      refine ⟨74896504772851108714143269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199724012727602956571048717 74896504772851108714143269)
      ·
        refine ⟨14043094644909582883901863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74896504772851108714143269 14043094644909582883901863)
        ·
          refine ⟨21064641967364374325852795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043094644909582883901863 21064641967364374325852795)
          ·
            refine ⟨31596962951046561488779193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21064641967364374325852795 31596962951046561488779193)
            ·
              refine ⟨23697722213284921116584395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31596962951046561488779193 23697722213284921116584395)
              ·
                refine ⟨35546583319927381674876593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23697722213284921116584395 35546583319927381674876593)
                ·
                  refine ⟨26659937489945536256157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35546583319927381674876593 26659937489945536256157445)
                  ·
                    refine ⟨4998738279364788048029521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26659937489945536256157445 4998738279364788048029521)
                    ·
                      refine ⟨3749053709523591036022141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998738279364788048029521 3749053709523591036022141)
                      ·
                        rfl

theorem cell23_7301256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7301256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301256 prefixEnd_7301256 := by exact prefixLift 7301256
  have htrace : WordTrace (prefixWord ++ tailWord_7301256) baseStart_7301256 baseEnd_7301256 := by
    simpa [prefixWord, tailWord_7301256, baseEnd_7301256] using wordTrace_append hprefix tailTrace_7301256
  have hstable : (prefixWord ++ tailWord_7301256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301256).length < 2 ^ (prefixWord ++ tailWord_7301256).sum := by decide
  have hdescent : baseEnd_7301256 < baseStart_7301256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301306 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_7301306 : Nat := 118140960795 + 7301306 * 2 ^ 59
def prefixEnd_7301306 : Nat := 4983230072969 + 3 ^ 40 * 7301306 * 2
def baseEnd_7301306 : Nat := 3749079383556315840396911

theorem tailTrace_7301306 : CollatzResearch.WordTrace tailWord_7301306 prefixEnd_7301306 3749079383556315840396911 := by
  unfold tailWord_7301306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66575126821655700158512943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177533671524415200422701181 66575126821655700158512943)
  ·
    refine ⟨99862690232483550237769415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66575126821655700158512943 99862690232483550237769415)
    ·
      refine ⟨149794035348725325356654123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99862690232483550237769415 149794035348725325356654123)
      ·
        refine ⟨224691053023087988034981185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149794035348725325356654123 224691053023087988034981185)
        ·
          refine ⟨168518289767315991026235889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224691053023087988034981185 168518289767315991026235889)
          ·
            refine ⟨126388717325486993269676917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168518289767315991026235889 126388717325486993269676917)
            ·
              refine ⟨11848942249264405619032211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126388717325486993269676917 11848942249264405619032211)
              ·
                refine ⟨17773413373896608428548317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848942249264405619032211 17773413373896608428548317)
                ·
                  refine ⟨6665030015211228160705619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17773413373896608428548317 6665030015211228160705619)
                  ·
                    refine ⟨9997545022816842241058429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665030015211228160705619 9997545022816842241058429)
                    ·
                      refine ⟨3749079383556315840396911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9997545022816842241058429 3749079383556315840396911)
                      ·
                        rfl

theorem cell23_7301306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_7301306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301306 prefixEnd_7301306 := by exact prefixLift 7301306
  have htrace : WordTrace (prefixWord ++ tailWord_7301306) baseStart_7301306 baseEnd_7301306 := by
    simpa [prefixWord, tailWord_7301306, baseEnd_7301306] using wordTrace_append hprefix tailTrace_7301306
  have hstable : (prefixWord ++ tailWord_7301306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301306).length < 2 ^ (prefixWord ++ tailWord_7301306).sum := by decide
  have hdescent : baseEnd_7301306 < baseStart_7301306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301326 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_7301326 : Nat := 118140960795 + 7301326 * 2 ^ 59
def prefixEnd_7301326 : Nat := 4983230072969 + 3 ^ 40 * 7301326 * 2
def baseEnd_7301326 : Nat := 1249696551056468587382273

theorem tailTrace_7301326 : CollatzResearch.WordTrace tailWord_7301326 prefixEnd_7301326 1249696551056468587382273 := by
  unfold tailWord_7301326
  simp only [CollatzResearch.WordTrace]
  refine ⟨33287654593318793006222479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177534157831033562699853221 33287654593318793006222479)
  ·
    refine ⟨49931481889978189509333719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33287654593318793006222479 49931481889978189509333719)
    ·
      refine ⟨74897222834967284264000579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49931481889978189509333719 74897222834967284264000579)
      ·
        refine ⟨112345834252450926396000869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74897222834967284264000579 112345834252450926396000869)
        ·
          refine ⟨21064843922334548699250163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112345834252450926396000869 21064843922334548699250163)
          ·
            refine ⟨31597265883501823048875245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21064843922334548699250163 31597265883501823048875245)
            ·
              refine ⟨11848974706313183643328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31597265883501823048875245 11848974706313183643328217)
              ·
                refine ⟨8886731029734887732496163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11848974706313183643328217 8886731029734887732496163)
                ·
                  refine ⟨13330096544602331598744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8886731029734887732496163 13330096544602331598744245)
                  ·
                    refine ⟨1249696551056468587382273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13330096544602331598744245 1249696551056468587382273)
                    ·
                      rfl

theorem cell23_7301326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_7301326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301326 prefixEnd_7301326 := by exact prefixLift 7301326
  have htrace : WordTrace (prefixWord ++ tailWord_7301326) baseStart_7301326 baseEnd_7301326 := by
    simpa [prefixWord, tailWord_7301326, baseEnd_7301326] using wordTrace_append hprefix tailTrace_7301326
  have hstable : (prefixWord ++ tailWord_7301326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301326).length < 2 ^ (prefixWord ++ tailWord_7301326).sum := by decide
  have hdescent : baseEnd_7301326 < baseStart_7301326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301329 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_7301329 : Nat := 118140960795 + 7301329 * 2 ^ 59
def prefixEnd_7301329 : Nat := 4983230072969 + 3 ^ 40 * 7301329 * 2
def baseEnd_7301329 : Nat := 3749091193611369250409305

theorem tailTrace_7301329 : CollatzResearch.WordTrace tailWord_7301329 prefixEnd_7301329 3749091193611369250409305 := by
  unfold tailWord_7301329
  simp only [CollatzResearch.WordTrace]
  refine ⟨266301346165539475562139041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177534230777026317041426027 266301346165539475562139041)
  ·
    refine ⟨199726009624154606671604281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266301346165539475562139041 199726009624154606671604281)
    ·
      refine ⟨149794507218115955003703211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199726009624154606671604281 149794507218115955003703211)
      ·
        refine ⟨224691760827173932505554817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149794507218115955003703211 224691760827173932505554817)
        ·
          refine ⟨168518820620380449379166113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224691760827173932505554817 168518820620380449379166113)
          ·
            refine ⟨126389115465285337034374585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168518820620380449379166113 126389115465285337034374585)
            ·
              refine ⟨94791836598964002775780939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126389115465285337034374585 94791836598964002775780939)
              ·
                refine ⟨142187754898446004163671409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94791836598964002775780939 142187754898446004163671409)
                ·
                  refine ⟨106640816173834503122753557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142187754898446004163671409 106640816173834503122753557)
                  ·
                    refine ⟨4998788258148492333879073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106640816173834503122753557 4998788258148492333879073)
                    ·
                      refine ⟨3749091193611369250409305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998788258148492333879073 3749091193611369250409305)
                      ·
                        rfl

theorem cell23_7301329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_7301329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301329 prefixEnd_7301329 := by exact prefixLift 7301329
  have htrace : WordTrace (prefixWord ++ tailWord_7301329) baseStart_7301329 baseEnd_7301329 := by
    simpa [prefixWord, tailWord_7301329, baseEnd_7301329] using wordTrace_append hprefix tailTrace_7301329
  have hstable : (prefixWord ++ tailWord_7301329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301329).length < 2 ^ (prefixWord ++ tailWord_7301329).sum := by decide
  have hdescent : baseEnd_7301329 < baseStart_7301329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301352 : List Nat := [2, 1, 4, 1, 2, 13]
def baseStart_7301352 : Nat := 118140960795 + 7301352 * 2 ^ 59
def prefixEnd_7301352 : Nat := 4983230072969 + 3 ^ 40 * 7301352 * 2
def baseEnd_7301352 : Nat := 15428407422495566503793

theorem tailTrace_7301352 : CollatzResearch.WordTrace tailWord_7301352 prefixEnd_7301352 15428407422495566503793 := by
  unfold tailWord_7301352
  simp only [CollatzResearch.WordTrace]
  refine ⟨133151092522228075245113155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177534790029637433660150873 133151092522228075245113155)
  ·
    refine ⟨199726638783342112867669733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133151092522228075245113155 199726638783342112867669733)
    ·
      refine ⟨37448744771876646162688075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199726638783342112867669733 37448744771876646162688075)
      ·
        refine ⟨56173117157814969244032113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448744771876646162688075 56173117157814969244032113)
        ·
          refine ⟨42129837868361226933024085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56173117157814969244032113 42129837868361226933024085)
          ·
            refine ⟨15428407422495566503793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42129837868361226933024085 15428407422495566503793)
            ·
              rfl

theorem cell23_7301352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 13].length) (baseStart_7301352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301352 prefixEnd_7301352 := by exact prefixLift 7301352
  have htrace : WordTrace (prefixWord ++ tailWord_7301352) baseStart_7301352 baseEnd_7301352 := by
    simpa [prefixWord, tailWord_7301352, baseEnd_7301352] using wordTrace_append hprefix tailTrace_7301352
  have hstable : (prefixWord ++ tailWord_7301352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301352).length < 2 ^ (prefixWord ++ tailWord_7301352).sum := by decide
  have hdescent : baseEnd_7301352 < baseStart_7301352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301356 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_7301356 : Nat := 118140960795 + 7301356 * 2 ^ 59
def prefixEnd_7301356 : Nat := 4983230072969 + 3 ^ 40 * 7301356 * 2
def baseEnd_7301356 : Nat := 1249701685863013548257227

theorem tailTrace_7301356 : CollatzResearch.WordTrace tailWord_7301356 prefixEnd_7301356 1249701685863013548257227 := by
  unfold tailWord_7301356
  simp only [CollatzResearch.WordTrace]
  refine ⟨133151165468220829586685961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177534887290961106115581281 133151165468220829586685961)
  ·
    refine ⟨99863374101165622190014471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133151165468220829586685961 99863374101165622190014471)
    ·
      refine ⟨149795061151748433285021707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99863374101165622190014471 149795061151748433285021707)
      ·
        refine ⟨224692591727622649927532561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149795061151748433285021707 224692591727622649927532561)
        ·
          refine ⟨168519443795716987445649421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224692591727622649927532561 168519443795716987445649421)
          ·
            refine ⟨63194791423393870292118533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168519443795716987445649421 63194791423393870292118533)
            ·
              refine ⟨11849023391886350679772225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63194791423393870292118533 11849023391886350679772225)
              ·
                refine ⟨8886767543914763009829169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11849023391886350679772225 8886767543914763009829169)
                ·
                  refine ⟨6665075657936072257371877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8886767543914763009829169 6665075657936072257371877)
                  ·
                    refine ⟨1249701685863013548257227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665075657936072257371877 1249701685863013548257227)
                    ·
                      rfl

theorem cell23_7301356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_7301356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301356 prefixEnd_7301356 := by exact prefixLift 7301356
  have htrace : WordTrace (prefixWord ++ tailWord_7301356) baseStart_7301356 baseEnd_7301356 := by
    simpa [prefixWord, tailWord_7301356, baseEnd_7301356] using wordTrace_append hprefix tailTrace_7301356
  have hstable : (prefixWord ++ tailWord_7301356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301356).length < 2 ^ (prefixWord ++ tailWord_7301356).sum := by decide
  have hdescent : baseEnd_7301356 < baseStart_7301356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301366 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7301366 : Nat := 118140960795 + 7301366 * 2 ^ 59
def prefixEnd_7301366 : Nat := 4983230072969 + 3 ^ 40 * 7301366 * 2
def baseEnd_7301366 : Nat := 3749110192395585605646635

theorem tailTrace_7301366 : CollatzResearch.WordTrace tailWord_7301366 prefixEnd_7301366 3749110192395585605646635 := by
  unfold tailWord_7301366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643918479150339430077247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177535130444270287254157301 16643918479150339430077247)
  ·
    refine ⟨24965877718725509145115871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16643918479150339430077247 24965877718725509145115871)
    ·
      refine ⟨37448816578088263717673807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24965877718725509145115871 37448816578088263717673807)
      ·
        refine ⟨56173224867132395576510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448816578088263717673807 56173224867132395576510711)
        ·
          refine ⟨84259837300698593364766067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56173224867132395576510711 84259837300698593364766067)
          ·
            refine ⟨126389755951047890047149101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84259837300698593364766067 126389755951047890047149101)
            ·
              refine ⟨47396158481642958767680913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126389755951047890047149101 47396158481642958767680913)
              ·
                refine ⟨35547118861232219075760685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47396158481642958767680913 35547118861232219075760685)
                ·
                  refine ⟨13330169572962082153410257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35547118861232219075760685 13330169572962082153410257)
                  ·
                    refine ⟨9997627179721561615057693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13330169572962082153410257 9997627179721561615057693)
                    ·
                      refine ⟨3749110192395585605646635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9997627179721561615057693 3749110192395585605646635)
                      ·
                        rfl

theorem cell23_7301366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7301366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301366 prefixEnd_7301366 := by exact prefixLift 7301366
  have htrace : WordTrace (prefixWord ++ tailWord_7301366) baseStart_7301366 baseEnd_7301366 := by
    simpa [prefixWord, tailWord_7301366, baseEnd_7301366] using wordTrace_append hprefix tailTrace_7301366
  have hstable : (prefixWord ++ tailWord_7301366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301366).length < 2 ^ (prefixWord ++ tailWord_7301366).sum := by decide
  have hdescent : baseEnd_7301366 < baseStart_7301366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301380 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_7301380 : Nat := 118140960795 + 7301380 * 2 ^ 59
def prefixEnd_7301380 : Nat := 4983230072969 + 3 ^ 40 * 7301380 * 2
def baseEnd_7301380 : Nat := 3749117381124748550871571

theorem tailTrace_7301380 : CollatzResearch.WordTrace tailWord_7301380 prefixEnd_7301380 3749117381124748550871571 := by
  unfold tailWord_7301380
  simp only [CollatzResearch.WordTrace]
  refine ⟨133151603144177355636122797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177535470858903140848163729 133151603144177355636122797)
  ·
    refine ⟨49931851179066508363546049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133151603144177355636122797 49931851179066508363546049)
    ·
      refine ⟨37448888384299881272659537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49931851179066508363546049 37448888384299881272659537)
      ·
        refine ⟨28086666288224910954494653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37448888384299881272659537 28086666288224910954494653)
        ·
          refine ⟨10532499858084341607935495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28086666288224910954494653 10532499858084341607935495)
          ·
            refine ⟨15798749787126512411903243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532499858084341607935495 15798749787126512411903243)
            ·
              refine ⟨23698124680689768617854865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798749787126512411903243 23698124680689768617854865)
              ·
                refine ⟨17773593510517326463391149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23698124680689768617854865 17773593510517326463391149)
                ·
                  refine ⟨6665097566443997423771681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17773593510517326463391149 6665097566443997423771681)
                  ·
                    refine ⟨4998823174832998067828761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665097566443997423771681 4998823174832998067828761)
                    ·
                      refine ⟨3749117381124748550871571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998823174832998067828761 3749117381124748550871571)
                      ·
                        rfl

theorem cell23_7301380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_7301380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301380 prefixEnd_7301380 := by exact prefixLift 7301380
  have htrace : WordTrace (prefixWord ++ tailWord_7301380) baseStart_7301380 baseEnd_7301380 := by
    simpa [prefixWord, tailWord_7301380, baseEnd_7301380] using wordTrace_append hprefix tailTrace_7301380
  have hstable : (prefixWord ++ tailWord_7301380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301380).length < 2 ^ (prefixWord ++ tailWord_7301380).sum := by decide
  have hdescent : baseEnd_7301380 < baseStart_7301380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301413 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_7301413 : Nat := 118140960795 + 7301413 * 2 ^ 59
def prefixEnd_7301413 : Nat := 4983230072969 + 3 ^ 40 * 7301413 * 2
def baseEnd_7301413 : Nat := 3749134325986346921758919

theorem tailTrace_7301413 : CollatzResearch.WordTrace tailWord_7301413 prefixEnd_7301413 3749134325986346921758919 := by
  unfold tailWord_7301413
  simp only [CollatzResearch.WordTrace]
  refine ⟨266304409897235157908196893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177536273264823438605464595 266304409897235157908196893)
  ·
    refine ⟨99864153711463184215573835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266304409897235157908196893 99864153711463184215573835)
    ·
      refine ⟨149796230567194776323360753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99864153711463184215573835 149796230567194776323360753)
      ·
        refine ⟨112347172925396082242520565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149796230567194776323360753 112347172925396082242520565)
        ·
          refine ⟨10532547461755882710236303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112347172925396082242520565 10532547461755882710236303)
          ·
            refine ⟨15798821192633824065354455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532547461755882710236303 15798821192633824065354455)
            ·
              refine ⟨23698231788950736098031683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798821192633824065354455 23698231788950736098031683)
              ·
                refine ⟨35547347683426104147047525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23698231788950736098031683 35547347683426104147047525)
                ·
                  refine ⟨6665127690642394527571411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35547347683426104147047525 6665127690642394527571411)
                  ·
                    refine ⟨9997691535963591791357117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665127690642394527571411 9997691535963591791357117)
                    ·
                      refine ⟨3749134325986346921758919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9997691535963591791357117 3749134325986346921758919)
                      ·
                        rfl

theorem cell23_7301413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_7301413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301413 prefixEnd_7301413 := by exact prefixLift 7301413
  have htrace : WordTrace (prefixWord ++ tailWord_7301413) baseStart_7301413 baseEnd_7301413 := by
    simpa [prefixWord, tailWord_7301413, baseEnd_7301413] using wordTrace_append hprefix tailTrace_7301413
  have hstable : (prefixWord ++ tailWord_7301413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301413).length < 2 ^ (prefixWord ++ tailWord_7301413).sum := by decide
  have hdescent : baseEnd_7301413 < baseStart_7301413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301429 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7301429 : Nat := 118140960795 + 7301429 * 2 ^ 59
def prefixEnd_7301429 : Nat := 4983230072969 + 3 ^ 40 * 7301429 * 2
def baseEnd_7301429 : Nat := 1249714180558939619719615

theorem tailTrace_7301429 : CollatzResearch.WordTrace tailWord_7301429 prefixEnd_7301429 1249714180558939619719615 := by
  unfold tailWord_7301429
  simp only [CollatzResearch.WordTrace]
  refine ⟨266304993465177192640779341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177536662310118128427186227 266304993465177192640779341)
  ·
    refine ⟨99864372549441447240292253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266304993465177192640779341 99864372549441447240292253)
    ·
      refine ⟨37449139706040542715109595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99864372549441447240292253 37449139706040542715109595)
      ·
        refine ⟨56173709559060814072664393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37449139706040542715109595 56173709559060814072664393)
        ·
          refine ⟨42130282169295610554498295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56173709559060814072664393 42130282169295610554498295)
          ·
            refine ⟨63195423253943415831747443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42130282169295610554498295 63195423253943415831747443)
            ·
              refine ⟨94793134880915123747621165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63195423253943415831747443 94793134880915123747621165)
              ·
                refine ⟨35547425580343171405357937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94793134880915123747621165 35547425580343171405357937)
                ·
                  refine ⟨26660569185257378554018453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35547425580343171405357937 26660569185257378554018453)
                  ·
                    refine ⟨1249714180558939619719615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26660569185257378554018453 1249714180558939619719615)
                    ·
                      rfl

theorem cell23_7301429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7301429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301429 prefixEnd_7301429 := by exact prefixLift 7301429
  have htrace : WordTrace (prefixWord ++ tailWord_7301429) baseStart_7301429 baseEnd_7301429 := by
    simpa [prefixWord, tailWord_7301429, baseEnd_7301429] using wordTrace_append hprefix tailTrace_7301429
  have hstable : (prefixWord ++ tailWord_7301429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301429).length < 2 ^ (prefixWord ++ tailWord_7301429).sum := by decide
  have hdescent : baseEnd_7301429 < baseStart_7301429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301439 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_7301439 : Nat := 118140960795 + 7301439 * 2 ^ 59
def prefixEnd_7301439 : Nat := 4983230072969 + 3 ^ 40 * 7301439 * 2
def baseEnd_7301439 : Nat := 3749147676483363820033799

theorem tailTrace_7301439 : CollatzResearch.WordTrace tailWord_7301439 prefixEnd_7301439 3749147676483363820033799 := by
  unfold tailWord_7301439
  simp only [CollatzResearch.WordTrace]
  refine ⟨266305358195140964348643371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177536905463427309565762247 266305358195140964348643371)
  ·
    refine ⟨399458037292711446522965057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266305358195140964348643371 399458037292711446522965057)
    ·
      refine ⟨299593527969533584892223793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399458037292711446522965057 299593527969533584892223793)
      ·
        refine ⟨224695145977150188669167845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299593527969533584892223793 224695145977150188669167845)
        ·
          refine ⟨42130339870715660375468971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224695145977150188669167845 42130339870715660375468971)
          ·
            refine ⟨63195509806073490563203457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42130339870715660375468971 63195509806073490563203457)
            ·
              refine ⟨47396632354555117922402593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63195509806073490563203457 47396632354555117922402593)
              ·
                refine ⟨35547474265916338441801945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47396632354555117922402593 35547474265916338441801945)
                ·
                  refine ⟨26660605699437253831351459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35547474265916338441801945 26660605699437253831351459)
                  ·
                    refine ⟨39990908549155880747027189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26660605699437253831351459 39990908549155880747027189)
                    ·
                      refine ⟨3749147676483363820033799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39990908549155880747027189 3749147676483363820033799)
                      ·
                        rfl

theorem cell23_7301439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_7301439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301439 prefixEnd_7301439 := by exact prefixLift 7301439
  have htrace : WordTrace (prefixWord ++ tailWord_7301439) baseStart_7301439 baseEnd_7301439 := by
    simpa [prefixWord, tailWord_7301439, baseEnd_7301439] using wordTrace_append hprefix tailTrace_7301439
  have hstable : (prefixWord ++ tailWord_7301439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301439).length < 2 ^ (prefixWord ++ tailWord_7301439).sum := by decide
  have hdescent : baseEnd_7301439 < baseStart_7301439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301489 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_7301489 : Nat := 118140960795 + 7301489 * 2 ^ 59
def prefixEnd_7301489 : Nat := 4983230072969 + 3 ^ 40 * 7301489 * 2
def baseEnd_7301489 : Nat := 1249724450172029541469523

theorem tailTrace_7301489 : CollatzResearch.WordTrace tailWord_7301489 prefixEnd_7301489 1249724450172029541469523 := by
  unfold tailWord_7301489
  simp only [CollatzResearch.WordTrace]
  refine ⟨266307181844959822887963521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177538121229973215258642347 266307181844959822887963521)
  ·
    refine ⟨199730386383719867165972641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266307181844959822887963521 199730386383719867165972641)
    ·
      refine ⟨149797789787789900374479481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199730386383719867165972641 149797789787789900374479481)
      ·
        refine ⟨112348342340842425280859611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149797789787789900374479481 112348342340842425280859611)
        ·
          refine ⟨168522513511263637921289417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112348342340842425280859611 168522513511263637921289417)
          ·
            refine ⟨126391885133447728440967063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168522513511263637921289417 126391885133447728440967063)
            ·
              refine ⟨189587827700171592661450595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126391885133447728440967063 189587827700171592661450595)
              ·
                refine ⟨284381741550257388992175893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189587827700171592661450595 284381741550257388992175893)
                ·
                  refine ⟨13330394135168315109008245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284381741550257388992175893 13330394135168315109008245)
                  ·
                    refine ⟨1249724450172029541469523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13330394135168315109008245 1249724450172029541469523)
                    ·
                      rfl

theorem cell23_7301489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_7301489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301489 prefixEnd_7301489 := by exact prefixLift 7301489
  have htrace : WordTrace (prefixWord ++ tailWord_7301489) baseStart_7301489 baseEnd_7301489 := by
    simpa [prefixWord, tailWord_7301489, baseEnd_7301489] using wordTrace_append hprefix tailTrace_7301489
  have hstable : (prefixWord ++ tailWord_7301489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301489).length < 2 ^ (prefixWord ++ tailWord_7301489).sum := by decide
  have hdescent : baseEnd_7301489 < baseStart_7301489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301529 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_7301529 : Nat := 118140960795 + 7301529 * 2 ^ 59
def prefixEnd_7301529 : Nat := 4983230072969 + 3 ^ 40 * 7301529 * 2
def baseEnd_7301529 : Nat := 3749193889742268467908385

theorem tailTrace_7301529 : CollatzResearch.WordTrace tailWord_7301529 prefixEnd_7301529 3749193889742268467908385 := by
  unfold tailWord_7301529
  simp only [CollatzResearch.WordTrace]
  refine ⟨266308640764814909719419641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177539093843209939812946427 266308640764814909719419641)
  ·
    refine ⟨199731480573611182289564731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266308640764814909719419641 199731480573611182289564731)
    ·
      refine ⟨299597220860416773434347097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199731480573611182289564731 299597220860416773434347097)
      ·
        refine ⟨224697915645312580075760323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299597220860416773434347097 224697915645312580075760323)
        ·
          refine ⟨337046873467968870113640485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224697915645312580075760323 337046873467968870113640485)
          ·
            refine ⟨63196288775244163146307591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337046873467968870113640485 63196288775244163146307591)
            ·
              refine ⟨94794433162866244719461387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63196288775244163146307591 94794433162866244719461387)
              ·
                refine ⟨142191649744299367079192081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94794433162866244719461387 142191649744299367079192081)
                ·
                  refine ⟨106643737308224525309394061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142191649744299367079192081 106643737308224525309394061)
                  ·
                    refine ⟨39991401490584196991022773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106643737308224525309394061 39991401490584196991022773)
                    ·
                      refine ⟨3749193889742268467908385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39991401490584196991022773 3749193889742268467908385)
                      ·
                        rfl

theorem cell23_7301529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_7301529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301529 prefixEnd_7301529 := by exact prefixLift 7301529
  have htrace : WordTrace (prefixWord ++ tailWord_7301529) baseStart_7301529 baseEnd_7301529 := by
    simpa [prefixWord, tailWord_7301529, baseEnd_7301529] using wordTrace_append hprefix tailTrace_7301529
  have hstable : (prefixWord ++ tailWord_7301529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301529).length < 2 ^ (prefixWord ++ tailWord_7301529).sum := by decide
  have hdescent : baseEnd_7301529 < baseStart_7301529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301543 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_7301543 : Nat := 118140960795 + 7301543 * 2 ^ 59
def prefixEnd_7301543 : Nat := 4983230072969 + 3 ^ 40 * 7301543 * 2
def baseEnd_7301543 : Nat := 3749201078471431413133321

theorem tailTrace_7301543 : CollatzResearch.WordTrace tailWord_7301543 prefixEnd_7301543 3749201078471431413133321 := by
  unfold tailWord_7301543
  simp only [CollatzResearch.WordTrace]
  refine ⟨266309151386764190110429283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177539434257842793406952855 266309151386764190110429283)
  ·
    refine ⟨399463727080146285165643925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266309151386764190110429283 399463727080146285165643925)
    ·
      refine ⟨18724862206881857117139559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 399463727080146285165643925 18724862206881857117139559)
      ·
        refine ⟨28087293310322785675709339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18724862206881857117139559 28087293310322785675709339)
        ·
          refine ⟨42130939965484178513564009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28087293310322785675709339 42130939965484178513564009)
          ·
            refine ⟨31598204974113133885173007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42130939965484178513564009 31598204974113133885173007)
            ·
              refine ⟨47397307461169700827759511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31598204974113133885173007 47397307461169700827759511)
              ·
                refine ⟨71095961191754551241639267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47397307461169700827759511 71095961191754551241639267)
                ·
                  refine ⟨106643941787631826862458901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71095961191754551241639267 106643941787631826862458901)
                  ·
                    refine ⟨4998934771295241884177761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106643941787631826862458901 4998934771295241884177761)
                    ·
                      refine ⟨3749201078471431413133321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4998934771295241884177761 3749201078471431413133321)
                      ·
                        rfl

theorem cell23_7301543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_7301543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301543 prefixEnd_7301543 := by exact prefixLift 7301543
  have htrace : WordTrace (prefixWord ++ tailWord_7301543) baseStart_7301543 baseEnd_7301543 := by
    simpa [prefixWord, tailWord_7301543, baseEnd_7301543] using wordTrace_append hprefix tailTrace_7301543
  have hstable : (prefixWord ++ tailWord_7301543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301543).length < 2 ^ (prefixWord ++ tailWord_7301543).sum := by decide
  have hdescent : baseEnd_7301543 < baseStart_7301543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301553 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_7301553 : Nat := 118140960795 + 7301553 * 2 ^ 59
def prefixEnd_7301553 : Nat := 4983230072969 + 3 ^ 40 * 7301553 * 2
def baseEnd_7301553 : Nat := 1249735404425992124669425

theorem tailTrace_7301553 : CollatzResearch.WordTrace tailWord_7301553 prefixEnd_7301553 1249735404425992124669425 := by
  unfold tailWord_7301553
  simp only [CollatzResearch.WordTrace]
  refine ⟨266309516116727961818293313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177539677411151974545528875 266309516116727961818293313)
  ·
    refine ⟨199732137087545971363719985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266309516116727961818293313 199732137087545971363719985)
    ·
      refine ⟨149799102815659478522789989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199732137087545971363719985 149799102815659478522789989)
      ·
        refine ⟨28087331777936152223023123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149799102815659478522789989 28087331777936152223023123)
        ·
          refine ⟨42130997666904228334534685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28087331777936152223023123 42130997666904228334534685)
          ·
            refine ⟨15799124125089085625450507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42130997666904228334534685 15799124125089085625450507)
            ·
              refine ⟨23698686187633628438175761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15799124125089085625450507 23698686187633628438175761)
              ·
                refine ⟨17774014640725221328631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23698686187633628438175761 17774014640725221328631821)
                ·
                  refine ⟨6665255490271957998236933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17774014640725221328631821 6665255490271957998236933)
                  ·
                    refine ⟨1249735404425992124669425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665255490271957998236933 1249735404425992124669425)
                    ·
                      rfl

theorem cell23_7301553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_7301553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301553 prefixEnd_7301553 := by exact prefixLift 7301553
  have htrace : WordTrace (prefixWord ++ tailWord_7301553) baseStart_7301553 baseEnd_7301553 := by
    simpa [prefixWord, tailWord_7301553, baseEnd_7301553] using wordTrace_append hprefix tailTrace_7301553
  have hstable : (prefixWord ++ tailWord_7301553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301553).length < 2 ^ (prefixWord ++ tailWord_7301553).sum := by decide
  have hdescent : baseEnd_7301553 < baseStart_7301553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301610 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_7301610 : Nat := 118140960795 + 7301610 * 2 ^ 59
def prefixEnd_7301610 : Nat := 4983230072969 + 3 ^ 40 * 7301610 * 2
def baseEnd_7301610 : Nat := 3749235481675282650995513

theorem tailTrace_7301610 : CollatzResearch.WordTrace tailWord_7301610 prefixEnd_7301610 3749235481675282650995513 := by
  unfold tailWord_7301610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66577898769380365138279571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177541063385014307035412189 66577898769380365138279571)
  ·
    refine ⟨99866848154070547707419357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66577898769380365138279571 99866848154070547707419357)
    ·
      refine ⟨37450068057776455390282259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99866848154070547707419357 37450068057776455390282259)
      ·
        refine ⟨56175102086664683085423389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37450068057776455390282259 56175102086664683085423389)
        ·
          refine ⟨21065663282499256157033771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56175102086664683085423389 21065663282499256157033771)
          ·
            refine ⟨31598494923748884235550657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21065663282499256157033771 31598494923748884235550657)
            ·
              refine ⟨23698871192811663176662993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31598494923748884235550657 23698871192811663176662993)
              ·
                refine ⟨17774153394608747382497245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23698871192811663176662993 17774153394608747382497245)
                ·
                  refine ⟨6665307522978280268436467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17774153394608747382497245 6665307522978280268436467)
                  ·
                    refine ⟨9997961284467420402654701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665307522978280268436467 9997961284467420402654701)
                    ·
                      refine ⟨3749235481675282650995513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9997961284467420402654701 3749235481675282650995513)
                      ·
                        rfl

theorem cell23_7301610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_7301610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301610 prefixEnd_7301610 := by exact prefixLift 7301610
  have htrace : WordTrace (prefixWord ++ tailWord_7301610) baseStart_7301610 baseEnd_7301610 := by
    simpa [prefixWord, tailWord_7301610, baseEnd_7301610] using wordTrace_append hprefix tailTrace_7301610
  have hstable : (prefixWord ++ tailWord_7301610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301610).length < 2 ^ (prefixWord ++ tailWord_7301610).sum := by decide
  have hdescent : baseEnd_7301610 < baseStart_7301610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301621 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7301621 : Nat := 118140960795 + 7301621 * 2 ^ 59
def prefixEnd_7301621 : Nat := 4983230072969 + 3 ^ 40 * 7301621 * 2
def baseEnd_7301621 : Nat := 1249747043320827369319321

theorem tailTrace_7301621 : CollatzResearch.WordTrace tailWord_7301621 prefixEnd_7301621 1249747043320827369319321 := by
  unfold tailWord_7301621
  simp only [CollatzResearch.WordTrace]
  refine ⟨266311996280481609431768717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177541330853654406287845811 266311996280481609431768717)
  ·
    refine ⟨99866998605180603536913269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266311996280481609431768717 99866998605180603536913269)
    ·
      refine ⟨9362531119235681581585619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99866998605180603536913269 9362531119235681581585619)
      ·
        refine ⟨14043796678853522372378429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362531119235681581585619 14043796678853522372378429)
        ·
          refine ⟨5266423754570070889641911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14043796678853522372378429 5266423754570070889641911)
          ·
            refine ⟨7899635631855106334462867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266423754570070889641911 7899635631855106334462867)
            ·
              refine ⟨11849453447782659501694301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899635631855106334462867 11849453447782659501694301)
              ·
                refine ⟨4443545042918497313135363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11849453447782659501694301 4443545042918497313135363)
                ·
                  refine ⟨6665317564377745969703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443545042918497313135363 6665317564377745969703045)
                  ·
                    refine ⟨1249747043320827369319321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665317564377745969703045 1249747043320827369319321)
                    ·
                      rfl

theorem cell23_7301621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7301621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301621 prefixEnd_7301621 := by exact prefixLift 7301621
  have htrace : WordTrace (prefixWord ++ tailWord_7301621) baseStart_7301621 baseEnd_7301621 := by
    simpa [prefixWord, tailWord_7301621, baseEnd_7301621] using wordTrace_append hprefix tailTrace_7301621
  have hstable : (prefixWord ++ tailWord_7301621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301621).length < 2 ^ (prefixWord ++ tailWord_7301621).sum := by decide
  have hdescent : baseEnd_7301621 < baseStart_7301621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301638 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7301638 : Nat := 118140960795 + 7301638 * 2 ^ 59
def prefixEnd_7301638 : Nat := 4983230072969 + 3 ^ 40 * 7301638 * 2
def baseEnd_7301638 : Nat := 1249749953044536180481795

theorem tailTrace_7301638 : CollatzResearch.WordTrace tailWord_7301638 prefixEnd_7301638 1249749953044536180481795 := by
  unfold tailWord_7301638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322269260044375666723049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177541744214280014223425045 8322269260044375666723049)
  ·
    refine ⟨6241701945033281750042287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8322269260044375666723049 6241701945033281750042287)
    ·
      refine ⟨9362552917549922625063431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241701945033281750042287 9362552917549922625063431)
      ·
        refine ⟨14043829376324883937595147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362552917549922625063431 14043829376324883937595147)
        ·
          refine ⟨21065744064487325906392721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043829376324883937595147 21065744064487325906392721)
          ·
            refine ⟨15799308048365494429794541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21065744064487325906392721 15799308048365494429794541)
            ·
              refine ⟨5924740518137060411172953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15799308048365494429794541 5924740518137060411172953)
              ·
                refine ⟨4443555388602795308379715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5924740518137060411172953 4443555388602795308379715)
                ·
                  refine ⟨6665333082904192962569573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443555388602795308379715 6665333082904192962569573)
                  ·
                    refine ⟨1249749953044536180481795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665333082904192962569573 1249749953044536180481795)
                    ·
                      rfl

theorem cell23_7301638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7301638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301638 prefixEnd_7301638 := by exact prefixLift 7301638
  have htrace : WordTrace (prefixWord ++ tailWord_7301638) baseStart_7301638 baseEnd_7301638 := by
    simpa [prefixWord, tailWord_7301638, baseEnd_7301638] using wordTrace_append hprefix tailTrace_7301638
  have hstable : (prefixWord ++ tailWord_7301638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301638).length < 2 ^ (prefixWord ++ tailWord_7301638).sum := by decide
  have hdescent : baseEnd_7301638 < baseStart_7301638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301643 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 4, 4]
def baseStart_7301643 : Nat := 118140960795 + 7301643 * 2 ^ 59
def prefixEnd_7301643 : Nat := 4983230072969 + 3 ^ 40 * 7301643 * 2
def baseEnd_7301643 : Nat := 1249750808845627007294287

theorem tailTrace_7301643 : CollatzResearch.WordTrace tailWord_7301643 prefixEnd_7301643 1249750808845627007294287 := by
  unfold tailWord_7301643
  simp only [CollatzResearch.WordTrace]
  refine ⟨266312798686401907189069583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177541865790934604792713055 266312798686401907189069583)
  ·
    refine ⟨399469198029602860783604375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266312798686401907189069583 399469198029602860783604375)
    ·
      refine ⟨599203797044404291175406563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399469198029602860783604375 599203797044404291175406563)
      ·
        refine ⟨898805695566606436763109845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599203797044404291175406563 898805695566606436763109845)
        ·
          refine ⟨21065758489842338361635387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 898805695566606436763109845 21065758489842338361635387)
          ·
            refine ⟨31598637734763507542453081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21065758489842338361635387 31598637734763507542453081)
            ·
              refine ⟨23698978301072630656839811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31598637734763507542453081 23698978301072630656839811)
              ·
                refine ⟨35548467451608945985259717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23698978301072630656839811 35548467451608945985259717)
                ·
                  refine ⟨6665337647176677372236197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35548467451608945985259717 6665337647176677372236197)
                  ·
                    refine ⟨1249750808845627007294287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665337647176677372236197 1249750808845627007294287)
                    ·
                      rfl

theorem cell23_7301643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 4].length) (baseStart_7301643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301643 prefixEnd_7301643 := by exact prefixLift 7301643
  have htrace : WordTrace (prefixWord ++ tailWord_7301643) baseStart_7301643 baseEnd_7301643 := by
    simpa [prefixWord, tailWord_7301643, baseEnd_7301643] using wordTrace_append hprefix tailTrace_7301643
  have hstable : (prefixWord ++ tailWord_7301643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301643).length < 2 ^ (prefixWord ++ tailWord_7301643).sum := by decide
  have hdescent : baseEnd_7301643 < baseStart_7301643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301644 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 1, 1, 3]
def baseStart_7301644 : Nat := 118140960795 + 7301644 * 2 ^ 59
def prefixEnd_7301644 : Nat := 4983230072969 + 3 ^ 40 * 7301644 * 2
def baseEnd_7301644 : Nat := 3749252940017535517970357

theorem tailTrace_7301644 : CollatzResearch.WordTrace tailWord_7301644 prefixEnd_7301644 3749252940017535517970357 := by
  unfold tailWord_7301644
  simp only [CollatzResearch.WordTrace]
  refine ⟨133156417579699142179927993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177541890106265522906570657 133156417579699142179927993)
  ·
    refine ⟨99867313184774356634945995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133156417579699142179927993 99867313184774356634945995)
    ·
      refine ⟨149800969777161534952418993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99867313184774356634945995 149800969777161534952418993)
      ·
        refine ⟨112350727332871151214314245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149800969777161534952418993 112350727332871151214314245)
        ·
          refine ⟨21065761374913340852683921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112350727332871151214314245 21065761374913340852683921)
          ·
            refine ⟨15799321031185005639512941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21065761374913340852683921 15799321031185005639512941)
            ·
              refine ⟨5924745386694377114817353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15799321031185005639512941 5924745386694377114817353)
              ·
                refine ⟨4443559040020782836113015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5924745386694377114817353 4443559040020782836113015)
                ·
                  refine ⟨6665338560031174254169523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443559040020782836113015 6665338560031174254169523)
                  ·
                    refine ⟨9998007840046761381254285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665338560031174254169523 9998007840046761381254285)
                    ·
                      refine ⟨3749252940017535517970357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998007840046761381254285 3749252940017535517970357)
                      ·
                        rfl

theorem cell23_7301644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_7301644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301644 prefixEnd_7301644 := by exact prefixLift 7301644
  have htrace : WordTrace (prefixWord ++ tailWord_7301644) baseStart_7301644 baseEnd_7301644 := by
    simpa [prefixWord, tailWord_7301644, baseEnd_7301644] using wordTrace_append hprefix tailTrace_7301644
  have hstable : (prefixWord ++ tailWord_7301644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301644).length < 2 ^ (prefixWord ++ tailWord_7301644).sum := by decide
  have hdescent : baseEnd_7301644 < baseStart_7301644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301653 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_7301653 : Nat := 118140960795 + 7301653 * 2 ^ 59
def prefixEnd_7301653 : Nat := 4983230072969 + 3 ^ 40 * 7301653 * 2
def baseEnd_7301653 : Nat := 3749257561343425982757815

theorem tailTrace_7301653 : CollatzResearch.WordTrace tailWord_7301653 prefixEnd_7301653 3749257561343425982757815 := by
  unfold tailWord_7301653
  simp only [CollatzResearch.WordTrace]
  refine ⟨266313163416365678896933613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177542108944243785931289075 266313163416365678896933613)
  ·
    refine ⟨99867436281137129586350105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266313163416365678896933613 99867436281137129586350105)
    ·
      refine ⟨74900577210852847189762579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99867436281137129586350105 74900577210852847189762579)
      ·
        refine ⟨112350865816279270784643869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74900577210852847189762579 112350865816279270784643869)
        ·
          refine ⟨42131574681104726544241451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112350865816279270784643869 42131574681104726544241451)
          ·
            refine ⟨63197362021657089816362177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42131574681104726544241451 63197362021657089816362177)
            ·
              refine ⟨47398021516242817362271633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63197362021657089816362177 47398021516242817362271633)
              ·
                refine ⟨35548516137182113021703725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47398021516242817362271633 35548516137182113021703725)
                ·
                  refine ⟨13330693551443292383138897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35548516137182113021703725 13330693551443292383138897)
                  ·
                    refine ⟨9998020163582469287354173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13330693551443292383138897 9998020163582469287354173)
                    ·
                      refine ⟨3749257561343425982757815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998020163582469287354173 3749257561343425982757815)
                      ·
                        rfl

theorem cell23_7301653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_7301653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301653 prefixEnd_7301653 := by exact prefixLift 7301653
  have htrace : WordTrace (prefixWord ++ tailWord_7301653) baseStart_7301653 baseEnd_7301653 := by
    simpa [prefixWord, tailWord_7301653, baseEnd_7301653] using wordTrace_append hprefix tailTrace_7301653
  have hstable : (prefixWord ++ tailWord_7301653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301653).length < 2 ^ (prefixWord ++ tailWord_7301653).sum := by decide
  have hdescent : baseEnd_7301653 < baseStart_7301653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301656 : List Nat := [2, 1, 2, 3, 3, 1, 1, 10]
def baseStart_7301656 : Nat := 118140960795 + 7301656 * 2 ^ 59
def prefixEnd_7301656 : Nat := 4983230072969 + 3 ^ 40 * 7301656 * 2
def baseEnd_7301656 : Nat := 138861448214273684111863

theorem tailTrace_7301656 : CollatzResearch.WordTrace tailWord_7301656 prefixEnd_7301656 138861448214273684111863 := by
  unfold tailWord_7301656
  simp only [CollatzResearch.WordTrace]
  refine ⟨133156636417677405204646411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177542181890236540272861881 133156636417677405204646411)
  ·
    refine ⟨199734954626516107806969617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133156636417677405204646411 199734954626516107806969617)
    ·
      refine ⟨149801215969887080855227213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199734954626516107806969617 149801215969887080855227213)
      ·
        refine ⟨56175455988707655320710205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149801215969887080855227213 56175455988707655320710205)
        ·
          refine ⟨21065795995765370745266327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56175455988707655320710205 21065795995765370745266327)
          ·
            refine ⟨31598693993648056117899491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21065795995765370745266327 31598693993648056117899491)
            ·
              refine ⟨47398040990472084176849237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31598693993648056117899491 47398040990472084176849237)
              ·
                refine ⟨138861448214273684111863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47398040990472084176849237 138861448214273684111863)
                ·
                  rfl

theorem cell23_7301656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 10].length) (baseStart_7301656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301656 prefixEnd_7301656 := by exact prefixLift 7301656
  have htrace : WordTrace (prefixWord ++ tailWord_7301656) baseStart_7301656 baseEnd_7301656 := by
    simpa [prefixWord, tailWord_7301656, baseEnd_7301656] using wordTrace_append hprefix tailTrace_7301656
  have hstable : (prefixWord ++ tailWord_7301656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301656).length < 2 ^ (prefixWord ++ tailWord_7301656).sum := by decide
  have hdescent : baseEnd_7301656 < baseStart_7301656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301660 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_7301660 : Nat := 118140960795 + 7301660 * 2 ^ 59
def prefixEnd_7301660 : Nat := 4983230072969 + 3 ^ 40 * 7301660 * 2
def baseEnd_7301660 : Nat := 1249753718569335818456761

theorem tailTrace_7301660 : CollatzResearch.WordTrace tailWord_7301660 prefixEnd_7301660 1249753718569335818456761 := by
  unfold tailWord_7301660
  simp only [CollatzResearch.WordTrace]
  refine ⟨133156709363670159546219217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177542279151560212728292289 133156709363670159546219217)
  ·
    refine ⟨99867532022752619659664413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133156709363670159546219217 99867532022752619659664413)
    ·
      refine ⟨37450324508532232372374155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99867532022752619659664413 37450324508532232372374155)
      ·
        refine ⟨56175486762798348558561233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37450324508532232372374155 56175486762798348558561233)
        ·
          refine ⟨42131615072098761418920925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56175486762798348558561233 42131615072098761418920925)
          ·
            refine ⟨15799355652037035532095347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42131615072098761418920925 15799355652037035532095347)
            ·
              refine ⟨23699033478055553298143021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15799355652037035532095347 23699033478055553298143021)
              ·
                refine ⟨8887137554270832486803633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23699033478055553298143021 8887137554270832486803633)
                ·
                  refine ⟨6665353165703124365102725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887137554270832486803633 6665353165703124365102725)
                  ·
                    refine ⟨1249753718569335818456761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665353165703124365102725 1249753718569335818456761)
                    ·
                      rfl

theorem cell23_7301660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_7301660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301660 prefixEnd_7301660 := by exact prefixLift 7301660
  have htrace : WordTrace (prefixWord ++ tailWord_7301660) baseStart_7301660 baseEnd_7301660 := by
    simpa [prefixWord, tailWord_7301660, baseEnd_7301660] using wordTrace_append hprefix tailTrace_7301660
  have hstable : (prefixWord ++ tailWord_7301660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301660).length < 2 ^ (prefixWord ++ tailWord_7301660).sum := by decide
  have hdescent : baseEnd_7301660 < baseStart_7301660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301683 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3]
def baseStart_7301683 : Nat := 118140960795 + 7301683 * 2 ^ 59
def prefixEnd_7301683 : Nat := 4983230072969 + 3 ^ 40 * 7301683 * 2
def baseEnd_7301683 : Nat := 3749272965763060865382677

theorem tailTrace_7301683 : CollatzResearch.WordTrace tailWord_7301683 prefixEnd_7301683 3749272965763060865382677 := by
  unfold tailWord_7301683
  simp only [CollatzResearch.WordTrace]
  refine ⟨266314257606256994020525703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177542838404171329347017135 266314257606256994020525703)
  ·
    refine ⟨399471386409385491030788555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266314257606256994020525703 399471386409385491030788555)
    ·
      refine ⟨599207079614078236546182833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399471386409385491030788555 599207079614078236546182833)
      ·
        refine ⟨449405309710558677409637125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599207079614078236546182833 449405309710558677409637125)
        ·
          refine ⟨84263495570729752014306961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449405309710558677409637125 84263495570729752014306961)
          ·
            refine ⟨63197621678047314010730221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84263495570729752014306961 63197621678047314010730221)
            ·
              refine ⟨23699108129267742754023833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63197621678047314010730221 23699108129267742754023833)
              ·
                refine ⟨17774331096950807065517875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23699108129267742754023833 17774331096950807065517875)
                ·
                  refine ⟨26661496645426210598276813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17774331096950807065517875 26661496645426210598276813)
                  ·
                    refine ⟨9998061242034828974353805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26661496645426210598276813 9998061242034828974353805)
                    ·
                      refine ⟨3749272965763060865382677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998061242034828974353805 3749272965763060865382677)
                      ·
                        rfl

theorem cell23_7301683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_7301683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301683 prefixEnd_7301683 := by exact prefixLift 7301683
  have htrace : WordTrace (prefixWord ++ tailWord_7301683) baseStart_7301683 baseEnd_7301683 := by
    simpa [prefixWord, tailWord_7301683, baseEnd_7301683] using wordTrace_append hprefix tailTrace_7301683
  have hstable : (prefixWord ++ tailWord_7301683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301683).length < 2 ^ (prefixWord ++ tailWord_7301683).sum := by decide
  have hdescent : baseEnd_7301683 < baseStart_7301683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301694 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_7301694 : Nat := 118140960795 + 7301694 * 2 ^ 59
def prefixEnd_7301694 : Nat := 4983230072969 + 3 ^ 40 * 7301694 * 2
def baseEnd_7301694 : Nat := 1249759538016753440781709

theorem tailTrace_7301694 : CollatzResearch.WordTrace tailWord_7301694 prefixEnd_7301694 1249759538016753440781709 := by
  unfold tailWord_7301694
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289332351152142862397017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177543105872811428599450757 33289332351152142862397017)
  ·
    refine ⟨24966999263364107146797763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33289332351152142862397017 24966999263364107146797763)
    ·
      refine ⟨37450498895046160720196645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24966999263364107146797763 37450498895046160720196645)
      ·
        refine ⟨7021968542821155135036871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37450498895046160720196645 7021968542821155135036871)
        ·
          refine ⟨10532952814231732702555307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021968542821155135036871 10532952814231732702555307)
          ·
            refine ⟨15799429221347599053832961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532952814231732702555307 15799429221347599053832961)
            ·
              refine ⟨11849571916010699290374721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15799429221347599053832961 11849571916010699290374721)
              ·
                refine ⟨8887178937008024467781041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11849571916010699290374721 8887178937008024467781041)
                ·
                  refine ⟨6665384202756018350835781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887178937008024467781041 6665384202756018350835781)
                  ·
                    refine ⟨1249759538016753440781709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665384202756018350835781 1249759538016753440781709)
                    ·
                      rfl

theorem cell23_7301694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_7301694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301694 prefixEnd_7301694 := by exact prefixLift 7301694
  have htrace : WordTrace (prefixWord ++ tailWord_7301694) baseStart_7301694 baseEnd_7301694 := by
    simpa [prefixWord, tailWord_7301694, baseEnd_7301694] using wordTrace_append hprefix tailTrace_7301694
  have hstable : (prefixWord ++ tailWord_7301694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301694).length < 2 ^ (prefixWord ++ tailWord_7301694).sum := by decide
  have hdescent : baseEnd_7301694 < baseStart_7301694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301696 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_7301696 : Nat := 118140960795 + 7301696 * 2 ^ 59
def prefixEnd_7301696 : Nat := 4983230072969 + 3 ^ 40 * 7301696 * 2
def baseEnd_7301696 : Nat := 3749279641011569314520117

theorem tailTrace_7301696 : CollatzResearch.WordTrace tailWord_7301696 prefixEnd_7301696 3749279641011569314520117 := by
  unfold tailWord_7301696
  simp only [CollatzResearch.WordTrace]
  refine ⟨133157365877604948620374471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177543154503473264827165961 133157365877604948620374471)
  ·
    refine ⟨199736048816407422930561707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133157365877604948620374471 199736048816407422930561707)
    ·
      refine ⟨299604073224611134395842561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199736048816407422930561707 299604073224611134395842561)
      ·
        refine ⟨224703054918458350796881921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299604073224611134395842561 224703054918458350796881921)
        ·
          refine ⟨168527291188843763097661441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224703054918458350796881921 168527291188843763097661441)
          ·
            refine ⟨126395468391632822323246081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168527291188843763097661441 126395468391632822323246081)
            ·
              refine ⟨94796601293724616742434561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126395468391632822323246081 94796601293724616742434561)
              ·
                refine ⟨71097450970293462556825921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94796601293724616742434561 71097450970293462556825921)
                ·
                  refine ⟨53323088227720096917619441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71097450970293462556825921 53323088227720096917619441)
                  ·
                    refine ⟨39992316170790072688214581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53323088227720096917619441 39992316170790072688214581)
                    ·
                      refine ⟨3749279641011569314520117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39992316170790072688214581 3749279641011569314520117)
                      ·
                        rfl

theorem cell23_7301696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_7301696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301696 prefixEnd_7301696 := by exact prefixLift 7301696
  have htrace : WordTrace (prefixWord ++ tailWord_7301696) baseStart_7301696 baseEnd_7301696 := by
    simpa [prefixWord, tailWord_7301696, baseEnd_7301696] using wordTrace_append hprefix tailTrace_7301696
  have hstable : (prefixWord ++ tailWord_7301696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301696).length < 2 ^ (prefixWord ++ tailWord_7301696).sum := by decide
  have hdescent : baseEnd_7301696 < baseStart_7301696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301701 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 1, 2, 2]
def baseStart_7301701 : Nat := 118140960795 + 7301701 * 2 ^ 59
def prefixEnd_7301701 : Nat := 4983230072969 + 3 ^ 40 * 7301701 * 2
def baseEnd_7301701 : Nat := 3749282208414841794957595

theorem tailTrace_7301701 : CollatzResearch.WordTrace tailWord_7301701 prefixEnd_7301701 3749282208414841794957595 := by
  unfold tailWord_7301701
  simp only [CollatzResearch.WordTrace]
  refine ⟨266314914120191783094680957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177543276080127855396453971 266314914120191783094680957)
  ·
    refine ⟨99868092795071918660505359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266314914120191783094680957 99868092795071918660505359)
    ·
      refine ⟨149802139192607877990758039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99868092795071918660505359 149802139192607877990758039)
      ·
        refine ⟨224703208788911816986137059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149802139192607877990758039 224703208788911816986137059)
        ·
          refine ⟨337054813183367725479205589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224703208788911816986137059 337054813183367725479205589)
          ·
            refine ⟨7899722183985181065918881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 337054813183367725479205589 7899722183985181065918881)
            ·
              refine ⟨5924791637988885799439161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7899722183985181065918881 5924791637988885799439161)
              ·
                refine ⟨4443593728491664349579371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5924791637988885799439161 4443593728491664349579371)
                ·
                  refine ⟨6665390592737496524369057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443593728491664349579371 6665390592737496524369057)
                  ·
                    refine ⟨4999042944553122393276793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665390592737496524369057 4999042944553122393276793)
                    ·
                      refine ⟨3749282208414841794957595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999042944553122393276793 3749282208414841794957595)
                      ·
                        rfl

theorem cell23_7301701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_7301701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301701 prefixEnd_7301701 := by exact prefixLift 7301701
  have htrace : WordTrace (prefixWord ++ tailWord_7301701) baseStart_7301701 baseEnd_7301701 := by
    simpa [prefixWord, tailWord_7301701, baseEnd_7301701] using wordTrace_append hprefix tailTrace_7301701
  have hstable : (prefixWord ++ tailWord_7301701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301701).length < 2 ^ (prefixWord ++ tailWord_7301701).sum := by decide
  have hdescent : baseEnd_7301701 < baseStart_7301701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301710 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_7301710 : Nat := 118140960795 + 7301710 * 2 ^ 59
def prefixEnd_7301710 : Nat := 4983230072969 + 3 ^ 40 * 7301710 * 2
def baseEnd_7301710 : Nat := 3749286829740732259745053

theorem tailTrace_7301710 : CollatzResearch.WordTrace tailWord_7301710 prefixEnd_7301710 3749286829740732259745053 := by
  unfold tailWord_7301710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289405297144897203969823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177543494918106118421172389 33289405297144897203969823)
  ·
    refine ⟨49934107945717345805954735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33289405297144897203969823 49934107945717345805954735)
    ·
      refine ⟨74901161918576018708932103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49934107945717345805954735 74901161918576018708932103)
      ·
        refine ⟨112351742877864028063398155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74901161918576018708932103 112351742877864028063398155)
        ·
          refine ⟨168527614316796042095097233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112351742877864028063398155 168527614316796042095097233)
          ·
            refine ⟨126395710737597031571322925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168527614316796042095097233 126395710737597031571322925)
            ·
              refine ⟨47398391526598886839246097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126395710737597031571322925 47398391526598886839246097)
              ·
                refine ⟨35548793644949165129434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47398391526598886839246097 35548793644949165129434573)
                ·
                  refine ⟨13330797616855936923537965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35548793644949165129434573 13330797616855936923537965)
                  ·
                    refine ⟨4999049106320976346326737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13330797616855936923537965 4999049106320976346326737)
                    ·
                      refine ⟨3749286829740732259745053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999049106320976346326737 3749286829740732259745053)
                      ·
                        rfl

theorem cell23_7301710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_7301710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301710 prefixEnd_7301710 := by exact prefixLift 7301710
  have htrace : WordTrace (prefixWord ++ tailWord_7301710) baseStart_7301710 baseEnd_7301710 := by
    simpa [prefixWord, tailWord_7301710, baseEnd_7301710] using wordTrace_append hprefix tailTrace_7301710
  have hstable : (prefixWord ++ tailWord_7301710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301710).length < 2 ^ (prefixWord ++ tailWord_7301710).sum := by decide
  have hdescent : baseEnd_7301710 < baseStart_7301710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301740 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_7301740 : Nat := 118140960795 + 7301740 * 2 ^ 59
def prefixEnd_7301740 : Nat := 4983230072969 + 3 ^ 40 * 7301740 * 2
def baseEnd_7301740 : Nat := 3749302234160367142369915

theorem tailTrace_7301740 : CollatzResearch.WordTrace tailWord_7301740 prefixEnd_7301740 3749302234160367142369915 := by
  unfold tailWord_7301740
  simp only [CollatzResearch.WordTrace]
  refine ⟨133158168283525246377675337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177544224378033661836900449 133158168283525246377675337)
  ·
    refine ⟨99868626212643934783256503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133158168283525246377675337 99868626212643934783256503)
    ·
      refine ⟨149802939318965902174884755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99868626212643934783256503 149802939318965902174884755)
      ·
        refine ⟨224704408978448853262327133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149802939318965902174884755 224704408978448853262327133)
        ·
          refine ⟨84264153366918319973372675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224704408978448853262327133 84264153366918319973372675)
          ·
            refine ⟨126396230050377479960059013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84264153366918319973372675 126396230050377479960059013)
            ·
              refine ⟨23699293134445777492511065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126396230050377479960059013 23699293134445777492511065)
              ·
                refine ⟨17774469850834333119383299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23699293134445777492511065 17774469850834333119383299)
                ·
                  refine ⟨26661704776251499679074949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17774469850834333119383299 26661704776251499679074949)
                  ·
                    refine ⟨4999069645547156189826553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26661704776251499679074949 4999069645547156189826553)
                    ·
                      refine ⟨3749302234160367142369915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999069645547156189826553 3749302234160367142369915)
                      ·
                        rfl

theorem cell23_7301740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_7301740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301740 prefixEnd_7301740 := by exact prefixLift 7301740
  have htrace : WordTrace (prefixWord ++ tailWord_7301740) baseStart_7301740 baseEnd_7301740 := by
    simpa [prefixWord, tailWord_7301740, baseEnd_7301740] using wordTrace_append hprefix tailTrace_7301740
  have hstable : (prefixWord ++ tailWord_7301740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301740).length < 2 ^ (prefixWord ++ tailWord_7301740).sum := by decide
  have hdescent : baseEnd_7301740 < baseStart_7301740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301753 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7301753 : Nat := 118140960795 + 7301753 * 2 ^ 59
def prefixEnd_7301753 : Nat := 4983230072969 + 3 ^ 40 * 7301753 * 2
def baseEnd_7301753 : Nat := 3749308909408875591507355

theorem tailTrace_7301753 : CollatzResearch.WordTrace tailWord_7301753 prefixEnd_7301753 3749308909408875591507355 := by
  unfold tailWord_7301753
  simp only [CollatzResearch.WordTrace]
  refine ⟨266316810716003395975573913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177544540477335597317049275 266316810716003395975573913)
  ·
    refine ⟨199737608037002546981680435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266316810716003395975573913 199737608037002546981680435)
    ·
      refine ⟨299606412055503820472520653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199737608037002546981680435 299606412055503820472520653)
      ·
        refine ⟨112352404520813932677195245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299606412055503820472520653 112352404520813932677195245)
        ·
          refine ⟨42132151695305224753948217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112352404520813932677195245 42132151695305224753948217)
          ·
            refine ⟨31599113771478918565461163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42132151695305224753948217 31599113771478918565461163)
            ·
              refine ⟨47398670657218377848191745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31599113771478918565461163 47398670657218377848191745)
              ·
                refine ⟨35549002992913783386143809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47398670657218377848191745 35549002992913783386143809)
                ·
                  refine ⟨26661752244685337539607857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35549002992913783386143809 26661752244685337539607857)
                  ·
                    refine ⟨19996314183514003154705893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26661752244685337539607857 19996314183514003154705893)
                    ·
                      refine ⟨3749308909408875591507355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19996314183514003154705893 3749308909408875591507355)
                      ·
                        rfl

theorem cell23_7301753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7301753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301753 prefixEnd_7301753 := by exact prefixLift 7301753
  have htrace : WordTrace (prefixWord ++ tailWord_7301753) baseStart_7301753 baseEnd_7301753 := by
    simpa [prefixWord, tailWord_7301753, baseEnd_7301753] using wordTrace_append hprefix tailTrace_7301753
  have hstable : (prefixWord ++ tailWord_7301753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301753).length < 2 ^ (prefixWord ++ tailWord_7301753).sum := by decide
  have hdescent : baseEnd_7301753 < baseStart_7301753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301780 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 7]
def baseStart_7301780 : Nat := 118140960795 + 7301780 * 2 ^ 59
def prefixEnd_7301780 : Nat := 4983230072969 + 3 ^ 40 * 7301780 * 2
def baseEnd_7301780 : Nat := 416591419265171887318859

theorem tailTrace_7301780 : CollatzResearch.WordTrace tailWord_7301780 prefixEnd_7301780 416591419265171887318859 := by
  unfold tailWord_7301780
  simp only [CollatzResearch.WordTrace]
  refine ⟨133158897743452789793403397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177545196991270386391204529 133158897743452789793403397)
  ·
    refine ⟨24967293326897398086263137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133158897743452789793403397 24967293326897398086263137)
    ·
      refine ⟨18725469995173048564697353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24967293326897398086263137 18725469995173048564697353)
      ·
        refine ⟨14044102496379786423523015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18725469995173048564697353 14044102496379786423523015)
        ·
          refine ⟨21066153744569679635284523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044102496379786423523015 21066153744569679635284523)
          ·
            refine ⟨31599230616854519452926785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21066153744569679635284523 31599230616854519452926785)
            ·
              refine ⟨23699422962640889589695089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31599230616854519452926785 23699422962640889589695089)
              ·
                refine ⟨17774567221980667192271317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23699422962640889589695089 17774567221980667192271317)
                ·
                  refine ⟨416591419265171887318859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17774567221980667192271317 416591419265171887318859)
                  ·
                    rfl

theorem cell23_7301780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_7301780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301780 prefixEnd_7301780 := by exact prefixLift 7301780
  have htrace : WordTrace (prefixWord ++ tailWord_7301780) baseStart_7301780 baseEnd_7301780 := by
    simpa [prefixWord, tailWord_7301780, baseEnd_7301780] using wordTrace_append hprefix tailTrace_7301780
  have hstable : (prefixWord ++ tailWord_7301780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301780).length < 2 ^ (prefixWord ++ tailWord_7301780).sum := by decide
  have hdescent : baseEnd_7301780 < baseStart_7301780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301814 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_7301814 : Nat := 118140960795 + 7301814 * 2 ^ 59
def prefixEnd_7301814 : Nat := 4983230072969 + 3 ^ 40 * 7301814 * 2
def baseEnd_7301814 : Nat := 416593359080977761427175

theorem tailTrace_7301814 : CollatzResearch.WordTrace tailWord_7301814 prefixEnd_7301814 416593359080977761427175 := by
  unfold tailWord_7301814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644939723048900212096531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177546023712521602262362997 16644939723048900212096531)
  ·
    refine ⟨24967409584573350318144797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16644939723048900212096531 24967409584573350318144797)
    ·
      refine ⟨9362778594215006369304299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24967409584573350318144797 9362778594215006369304299)
      ·
        refine ⟨14044167891322509553956449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362778594215006369304299 14044167891322509553956449)
        ·
          refine ⟨10533125918491882165467337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14044167891322509553956449 10533125918491882165467337)
          ·
            refine ⟨7899844438868911624100503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533125918491882165467337 7899844438868911624100503)
            ·
              refine ⟨11849766658303367436150755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899844438868911624100503 11849766658303367436150755)
              ·
                refine ⟨17774649987455051154226133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11849766658303367436150755 17774649987455051154226133)
                ·
                  refine ⟨416593359080977761427175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17774649987455051154226133 416593359080977761427175)
                  ·
                    rfl

theorem cell23_7301814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_7301814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301814 prefixEnd_7301814 := by exact prefixLift 7301814
  have htrace : WordTrace (prefixWord ++ tailWord_7301814) baseStart_7301814 baseEnd_7301814 := by
    simpa [prefixWord, tailWord_7301814, baseEnd_7301814] using wordTrace_append hprefix tailTrace_7301814
  have hstable : (prefixWord ++ tailWord_7301814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301814).length < 2 ^ (prefixWord ++ tailWord_7301814).sum := by decide
  have hdescent : baseEnd_7301814 < baseStart_7301814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301825 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7301825 : Nat := 118140960795 + 7301825 * 2 ^ 59
def prefixEnd_7301825 : Nat := 4983230072969 + 3 ^ 40 * 7301825 * 2
def baseEnd_7301825 : Nat := 3749345880015999309807025

theorem tailTrace_7301825 : CollatzResearch.WordTrace tailWord_7301825 prefixEnd_7301825 3749345880015999309807025 := by
  unfold tailWord_7301825
  simp only [CollatzResearch.WordTrace]
  refine ⟨266319436771742552272194929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177546291181161701514796619 266319436771742552272194929)
  ·
    refine ⟨199739577578806914204146197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266319436771742552272194929 199739577578806914204146197)
    ·
      refine ⟨9362792699006574103319353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199739577578806914204146197 9362792699006574103319353)
      ·
        refine ⟨7022094524254930577489515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9362792699006574103319353 7022094524254930577489515)
        ·
          refine ⟨10533141786382395866234273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022094524254930577489515 10533141786382395866234273)
          ·
            refine ⟨7899856339786796899675705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533141786382395866234273 7899856339786796899675705)
            ·
              refine ⟨5924892254840097674756779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7899856339786796899675705 5924892254840097674756779)
              ·
                refine ⟨8887338382260146512135169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924892254840097674756779 8887338382260146512135169)
                ·
                  refine ⟨6665503786695109884101377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887338382260146512135169 6665503786695109884101377)
                  ·
                    refine ⟨4999127840021332413076033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665503786695109884101377 4999127840021332413076033)
                    ·
                      refine ⟨3749345880015999309807025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999127840021332413076033 3749345880015999309807025)
                      ·
                        rfl

theorem cell23_7301825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7301825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301825 prefixEnd_7301825 := by exact prefixLift 7301825
  have htrace : WordTrace (prefixWord ++ tailWord_7301825) baseStart_7301825 baseEnd_7301825 := by
    simpa [prefixWord, tailWord_7301825, baseEnd_7301825] using wordTrace_append hprefix tailTrace_7301825
  have hstable : (prefixWord ++ tailWord_7301825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301825).length < 2 ^ (prefixWord ++ tailWord_7301825).sum := by decide
  have hdescent : baseEnd_7301825 < baseStart_7301825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301870 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_7301870 : Nat := 118140960795 + 7301870 * 2 ^ 59
def prefixEnd_7301870 : Nat := 4983230072969 + 3 ^ 40 * 7301870 * 2
def baseEnd_7301870 : Nat := 416596554071716848193813

theorem tailTrace_7301870 : CollatzResearch.WordTrace tailWord_7301870 prefixEnd_7301870 416596554071716848193813 := by
  unfold tailWord_7301870
  simp only [CollatzResearch.WordTrace]
  refine ⟨33290134757072440619697883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177547385371053016638388709 33290134757072440619697883)
  ·
    refine ⟨49935202135608660929546825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33290134757072440619697883 49935202135608660929546825)
    ·
      refine ⟨37451401601706495697160119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49935202135608660929546825 37451401601706495697160119)
      ·
        refine ⟨56177102402559743545740179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37451401601706495697160119 56177102402559743545740179)
        ·
          refine ⟨84265653603839615318610269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56177102402559743545740179 84265653603839615318610269)
          ·
            refine ⟨31599620101439855744478851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84265653603839615318610269 31599620101439855744478851)
            ·
              refine ⟨47399430152159783616718277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31599620101439855744478851 47399430152159783616718277)
              ·
                refine ⟨8887393153529959428134677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47399430152159783616718277 8887393153529959428134677)
                ·
                  refine ⟨416596554071716848193813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8887393153529959428134677 416596554071716848193813)
                  ·
                    rfl

theorem cell23_7301870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_7301870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301870 prefixEnd_7301870 := by exact prefixLift 7301870
  have htrace : WordTrace (prefixWord ++ tailWord_7301870) baseStart_7301870 baseEnd_7301870 := by
    simpa [prefixWord, tailWord_7301870, baseEnd_7301870] using wordTrace_append hprefix tailTrace_7301870
  have hstable : (prefixWord ++ tailWord_7301870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301870).length < 2 ^ (prefixWord ++ tailWord_7301870).sum := by decide
  have hdescent : baseEnd_7301870 < baseStart_7301870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301873 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_7301873 : Nat := 118140960795 + 7301873 * 2 ^ 59
def prefixEnd_7301873 : Nat := 4983230072969 + 3 ^ 40 * 7301873 * 2
def baseEnd_7301873 : Nat := 3749370527087415122006803

theorem tailTrace_7301873 : CollatzResearch.WordTrace tailWord_7301873 prefixEnd_7301873 3749370527087415122006803 := by
  unfold tailWord_7301873
  simp only [CollatzResearch.WordTrace]
  refine ⟨266321187475568656469942273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177547458317045770979961515 266321187475568656469942273)
  ·
    refine ⟨199740890606676492352456705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266321187475568656469942273 199740890606676492352456705)
    ·
      refine ⟨149805667955007369264342529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199740890606676492352456705 149805667955007369264342529)
      ·
        refine ⟨112354250966255526948256897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149805667955007369264342529 112354250966255526948256897)
        ·
          refine ⟨84265688224691645211192673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112354250966255526948256897 84265688224691645211192673)
          ·
            refine ⟨63199266168518733908394505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84265688224691645211192673 63199266168518733908394505)
            ·
              refine ⟨47399449626389050431295879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63199266168518733908394505 47399449626389050431295879)
              ·
                refine ⟨71099174439583575646943819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47399449626389050431295879 71099174439583575646943819)
                ·
                  refine ⟨106648761659375363470415729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71099174439583575646943819 106648761659375363470415729)
                  ·
                    refine ⟨79986571244531522602811797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106648761659375363470415729 79986571244531522602811797)
                    ·
                      refine ⟨3749370527087415122006803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79986571244531522602811797 3749370527087415122006803)
                      ·
                        rfl

theorem cell23_7301873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_7301873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301873 prefixEnd_7301873 := by exact prefixLift 7301873
  have htrace : WordTrace (prefixWord ++ tailWord_7301873) baseStart_7301873 baseEnd_7301873 := by
    simpa [prefixWord, tailWord_7301873, baseEnd_7301873] using wordTrace_append hprefix tailTrace_7301873
  have hstable : (prefixWord ++ tailWord_7301873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301873).length < 2 ^ (prefixWord ++ tailWord_7301873).sum := by decide
  have hdescent : baseEnd_7301873 < baseStart_7301873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301874 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_7301874 : Nat := 118140960795 + 7301874 * 2 ^ 59
def prefixEnd_7301874 : Nat := 4983230072969 + 3 ^ 40 * 7301874 * 2
def baseEnd_7301874 : Nat := 1249790346856023206031433

theorem tailTrace_7301874 : CollatzResearch.WordTrace tailWord_7301874 prefixEnd_7301874 1249790346856023206031433 := by
  unfold tailWord_7301874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66580305987141258410182169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177547482632376689093819117 66580305987141258410182169)
  ·
    refine ⟨49935229490355943807636627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66580305987141258410182169 49935229490355943807636627)
    ·
      refine ⟨74902844235533915711454941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49935229490355943807636627 74902844235533915711454941)
      ·
        refine ⟨28088566588325218391795603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74902844235533915711454941 28088566588325218391795603)
        ·
          refine ⟨42132849882487827587693405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28088566588325218391795603 42132849882487827587693405)
          ·
            refine ⟨15799818705932935345385027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42132849882487827587693405 15799818705932935345385027)
            ·
              refine ⟨23699728058899403018077541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15799818705932935345385027 23699728058899403018077541)
              ·
                refine ⟨4443699011043638065889539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23699728058899403018077541 4443699011043638065889539)
                ·
                  refine ⟨6665548516565457098834309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443699011043638065889539 6665548516565457098834309)
                  ·
                    refine ⟨1249790346856023206031433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665548516565457098834309 1249790346856023206031433)
                    ·
                      rfl

theorem cell23_7301874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_7301874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301874 prefixEnd_7301874 := by exact prefixLift 7301874
  have htrace : WordTrace (prefixWord ++ tailWord_7301874) baseStart_7301874 baseEnd_7301874 := by
    simpa [prefixWord, tailWord_7301874, baseEnd_7301874] using wordTrace_append hprefix tailTrace_7301874
  have hstable : (prefixWord ++ tailWord_7301874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301874).length < 2 ^ (prefixWord ++ tailWord_7301874).sum := by decide
  have hdescent : baseEnd_7301874 < baseStart_7301874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301900 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_7301900 : Nat := 118140960795 + 7301900 * 2 ^ 59
def prefixEnd_7301900 : Nat := 4983230072969 + 3 ^ 40 * 7301900 * 2
def baseEnd_7301900 : Nat := 1249794797021695505456393

theorem tailTrace_7301900 : CollatzResearch.WordTrace tailWord_7301900 prefixEnd_7301900 1249794797021695505456393 := by
  unfold tailWord_7301900
  simp only [CollatzResearch.WordTrace]
  refine ⟨133161086123235420040587577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177548114830980560054116769 133161086123235420040587577)
  ·
    refine ⟨99870814592426565030440683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133161086123235420040587577 99870814592426565030440683)
    ·
      refine ⟨149806221888639847545661025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99870814592426565030440683 149806221888639847545661025)
      ·
        refine ⟨112354666416479885659245769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149806221888639847545661025 112354666416479885659245769)
        ·
          refine ⟨84265999812359914244434327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112354666416479885659245769 84265999812359914244434327)
          ·
            refine ⟨126398999718539871366651491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84265999812359914244434327 126398999718539871366651491)
            ·
              refine ⟨189598499577809807049977237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126398999718539871366651491 189598499577809807049977237)
              ·
                refine ⟨8887429667709834705467683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189598499577809807049977237 8887429667709834705467683)
                ·
                  refine ⟨13331144501564752058201525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8887429667709834705467683 13331144501564752058201525)
                  ·
                    refine ⟨1249794797021695505456393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13331144501564752058201525 1249794797021695505456393)
                    ·
                      rfl

theorem cell23_7301900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_7301900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301900 prefixEnd_7301900 := by exact prefixLift 7301900
  have htrace : WordTrace (prefixWord ++ tailWord_7301900) baseStart_7301900 baseEnd_7301900 := by
    simpa [prefixWord, tailWord_7301900, baseEnd_7301900] using wordTrace_append hprefix tailTrace_7301900
  have hstable : (prefixWord ++ tailWord_7301900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301900).length < 2 ^ (prefixWord ++ tailWord_7301900).sum := by decide
  have hdescent : baseEnd_7301900 < baseStart_7301900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301913 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_7301913 : Nat := 118140960795 + 7301913 * 2 ^ 59
def prefixEnd_7301913 : Nat := 4983230072969 + 3 ^ 40 * 7301913 * 2
def baseEnd_7301913 : Nat := 1249797022104531655168873

theorem tailTrace_7301913 : CollatzResearch.WordTrace tailWord_7301913 prefixEnd_7301913 1249797022104531655168873 := by
  unfold tailWord_7301913
  simp only [CollatzResearch.WordTrace]
  refine ⟨266322646395423743301398393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177548430930282495534265595 266322646395423743301398393)
  ·
    refine ⟨199741984796567807476048795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266322646395423743301398393 199741984796567807476048795)
    ·
      refine ⟨299612977194851711214073193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199741984796567807476048795 299612977194851711214073193)
      ·
        refine ⟨224709732896138783410554895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299612977194851711214073193 224709732896138783410554895)
        ·
          refine ⟨337064599344208175115832343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224709732896138783410554895 337064599344208175115832343)
          ·
            refine ⟨505596899016312262673748515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337064599344208175115832343 505596899016312262673748515)
            ·
              refine ⟨758395348524468394010622773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505596899016312262673748515 758395348524468394010622773)
              ·
                refine ⟨71099563924168911938495885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 758395348524468394010622773 71099563924168911938495885)
                ·
                  refine ⟨26662336471563341976935957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71099563924168911938495885 26662336471563341976935957)
                  ·
                    refine ⟨1249797022104531655168873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26662336471563341976935957 1249797022104531655168873)
                    ·
                      rfl

theorem cell23_7301913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_7301913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301913 prefixEnd_7301913 := by exact prefixLift 7301913
  have htrace : WordTrace (prefixWord ++ tailWord_7301913) baseStart_7301913 baseEnd_7301913 := by
    simpa [prefixWord, tailWord_7301913, baseEnd_7301913] using wordTrace_append hprefix tailTrace_7301913
  have hstable : (prefixWord ++ tailWord_7301913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301913).length < 2 ^ (prefixWord ++ tailWord_7301913).sum := by decide
  have hdescent : baseEnd_7301913 < baseStart_7301913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301943 : List Nat := [1, 1, 3, 1, 2, 1, 4, 10]
def baseStart_7301943 : Nat := 118140960795 + 7301943 * 2 ^ 59
def prefixEnd_7301943 : Nat := 4983230072969 + 3 ^ 40 * 7301943 * 2
def baseEnd_7301943 : Nat := 138866906323452957338203

theorem tailTrace_7301943 : CollatzResearch.WordTrace tailWord_7301943 prefixEnd_7301943 138866906323452957338203 := by
  unfold tailWord_7301943
  simp only [CollatzResearch.WordTrace]
  refine ⟨266323740585315058424990483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177549160390210038949993655 266323740585315058424990483)
  ·
    refine ⟨399485610877972587637485725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266323740585315058424990483 399485610877972587637485725)
    ·
      refine ⟨149807104079239720364057147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399485610877972587637485725 149807104079239720364057147)
      ·
        refine ⟨224710656118859580546085721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149807104079239720364057147 224710656118859580546085721)
        ·
          refine ⟨168532992089144685409564291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224710656118859580546085721 168532992089144685409564291)
          ·
            refine ⟨252799488133717028114346437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168532992089144685409564291 252799488133717028114346437)
            ·
              refine ⟨47399904025071942771439957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252799488133717028114346437 47399904025071942771439957)
              ·
                refine ⟨138866906323452957338203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47399904025071942771439957 138866906323452957338203)
                ·
                  rfl

theorem cell23_7301943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 10].length) (baseStart_7301943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301943 prefixEnd_7301943 := by exact prefixLift 7301943
  have htrace : WordTrace (prefixWord ++ tailWord_7301943) baseStart_7301943 baseEnd_7301943 := by
    simpa [prefixWord, tailWord_7301943, baseEnd_7301943] using wordTrace_append hprefix tailTrace_7301943
  have hstable : (prefixWord ++ tailWord_7301943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301943).length < 2 ^ (prefixWord ++ tailWord_7301943).sum := by decide
  have hdescent : baseEnd_7301943 < baseStart_7301943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301963 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_7301963 : Nat := 118140960795 + 7301963 * 2 ^ 59
def prefixEnd_7301963 : Nat := 4983230072969 + 3 ^ 40 * 7301963 * 2
def baseEnd_7301963 : Nat := 3749416740346319769881389

theorem tailTrace_7301963 : CollatzResearch.WordTrace tailWord_7301963 prefixEnd_7301963 3749416740346319769881389 := by
  unfold tailWord_7301963
  simp only [CollatzResearch.WordTrace]
  refine ⟨266324470045242601840718543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177549646696828401227145695 266324470045242601840718543)
  ·
    refine ⟨399486705067863902761077815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266324470045242601840718543 399486705067863902761077815)
    ·
      refine ⟨599230057601795854141616723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399486705067863902761077815 599230057601795854141616723)
      ·
        refine ⟨898845086402693781212425085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599230057601795854141616723 898845086402693781212425085)
        ·
          refine ⟨337066907401010167954659407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898845086402693781212425085 337066907401010167954659407)
          ·
            refine ⟨505600361101515251931989111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337066907401010167954659407 505600361101515251931989111)
            ·
              refine ⟨758400541652272877897983667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505600361101515251931989111 758400541652272877897983667)
              ·
                refine ⟨1137600812478409316846975501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758400541652272877897983667 1137600812478409316846975501)
                ·
                  refine ⟨426600304679403493817615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137600812478409316846975501 426600304679403493817615813)
                  ·
                    refine ⟨79987557127388155090802965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426600304679403493817615813 79987557127388155090802965)
                    ·
                      refine ⟨3749416740346319769881389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79987557127388155090802965 3749416740346319769881389)
                      ·
                        rfl

theorem cell23_7301963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_7301963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301963 prefixEnd_7301963 := by exact prefixLift 7301963
  have htrace : WordTrace (prefixWord ++ tailWord_7301963) baseStart_7301963 baseEnd_7301963 := by
    simpa [prefixWord, tailWord_7301963, baseEnd_7301963] using wordTrace_append hprefix tailTrace_7301963
  have hstable : (prefixWord ++ tailWord_7301963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301963).length < 2 ^ (prefixWord ++ tailWord_7301963).sum := by decide
  have hdescent : baseEnd_7301963 < baseStart_7301963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301965 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7301965 : Nat := 118140960795 + 7301965 * 2 ^ 59
def prefixEnd_7301965 : Nat := 4983230072969 + 3 ^ 40 * 7301965 * 2
def baseEnd_7301965 : Nat := 3749417767307628762056381

theorem tailTrace_7301965 : CollatzResearch.WordTrace tailWord_7301965 prefixEnd_7301965 3749417767307628762056381 := by
  unfold tailWord_7301965
  simp only [CollatzResearch.WordTrace]
  refine ⟨266324542991235356182291349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177549695327490237454860899 266324542991235356182291349)
  ·
    refine ⟨12483962952714157321044907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266324542991235356182291349 12483962952714157321044907)
    ·
      refine ⟨18725944429071235981567361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12483962952714157321044907 18725944429071235981567361)
      ·
        refine ⟨14044458321803426986175521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18725944429071235981567361 14044458321803426986175521)
        ·
          refine ⟨10533343741352570239631641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14044458321803426986175521 10533343741352570239631641)
          ·
            refine ⟨7900007806014427679723731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533343741352570239631641 7900007806014427679723731)
            ·
              refine ⟨11850011709021641519585597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900007806014427679723731 11850011709021641519585597)
              ·
                refine ⟨4443754390883115569844599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11850011709021641519585597 4443754390883115569844599)
                ·
                  refine ⟨6665631586324673354766899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443754390883115569844599 6665631586324673354766899)
                  ·
                    refine ⟨9998447379487010032150349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665631586324673354766899 9998447379487010032150349)
                    ·
                      refine ⟨3749417767307628762056381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998447379487010032150349 3749417767307628762056381)
                      ·
                        rfl

theorem cell23_7301965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7301965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301965 prefixEnd_7301965 := by exact prefixLift 7301965
  have htrace : WordTrace (prefixWord ++ tailWord_7301965) baseStart_7301965 baseEnd_7301965 := by
    simpa [prefixWord, tailWord_7301965, baseEnd_7301965] using wordTrace_append hprefix tailTrace_7301965
  have hstable : (prefixWord ++ tailWord_7301965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301965).length < 2 ^ (prefixWord ++ tailWord_7301965).sum := by decide
  have hdescent : baseEnd_7301965 < baseStart_7301965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301997 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7301997 : Nat := 118140960795 + 7301997 * 2 ^ 59
def prefixEnd_7301997 : Nat := 4983230072969 + 3 ^ 40 * 7301997 * 2
def baseEnd_7301997 : Nat := 3749434198688572636856233

theorem tailTrace_7301997 : CollatzResearch.WordTrace tailWord_7301997 prefixEnd_7301997 3749434198688572636856233 := by
  unfold tailWord_7301997
  simp only [CollatzResearch.WordTrace]
  refine ⟨266325710127119425647456245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177550473418079617098304163 266325710127119425647456245)
  ·
    refine ⟨24968035324417446154449023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266325710127119425647456245 24968035324417446154449023)
    ·
      refine ⟨37452052986626169231673535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24968035324417446154449023 37452052986626169231673535)
      ·
        refine ⟨56178079479939253847510303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37452052986626169231673535 56178079479939253847510303)
        ·
          refine ⟨84267119219908880771265455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56178079479939253847510303 84267119219908880771265455)
          ·
            refine ⟨126400678829863321156898183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84267119219908880771265455 126400678829863321156898183)
            ·
              refine ⟨189601018244794981735347275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126400678829863321156898183 189601018244794981735347275)
              ·
                refine ⟨284401527367192472603020913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189601018244794981735347275 284401527367192472603020913)
                ·
                  refine ⟨213301145525394354452265685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284401527367192472603020913 213301145525394354452265685)
                  ·
                    refine ⟨4999245598251430182474977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213301145525394354452265685 4999245598251430182474977)
                    ·
                      refine ⟨3749434198688572636856233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999245598251430182474977 3749434198688572636856233)
                      ·
                        rfl

theorem cell23_7301997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7301997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301997 prefixEnd_7301997 := by exact prefixLift 7301997
  have htrace : WordTrace (prefixWord ++ tailWord_7301997) baseStart_7301997 baseEnd_7301997 := by
    simpa [prefixWord, tailWord_7301997, baseEnd_7301997] using wordTrace_append hprefix tailTrace_7301997
  have hstable : (prefixWord ++ tailWord_7301997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301997).length < 2 ^ (prefixWord ++ tailWord_7301997).sum := by decide
  have hdescent : baseEnd_7301997 < baseStart_7301997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7301998 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7301998 : Nat := 118140960795 + 7301998 * 2 ^ 59
def prefixEnd_7301998 : Nat := 4983230072969 + 3 ^ 40 * 7301998 * 2
def baseEnd_7301998 : Nat := 1249811570723075710981243

theorem tailTrace_7301998 : CollatzResearch.WordTrace tailWord_7301998 prefixEnd_7301998 1249811570723075710981243 := by
  unfold tailWord_7301998
  simp only [CollatzResearch.WordTrace]
  refine ⟨33290718325014475352280331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177550497733410535212161765 33290718325014475352280331)
  ·
    refine ⟨49936077487521713028420497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33290718325014475352280331 49936077487521713028420497)
    ·
      refine ⟨37452058115641284771315373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49936077487521713028420497 37452058115641284771315373)
      ·
        refine ⟨14044521793365481789243265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37452058115641284771315373 14044521793365481789243265)
        ·
          refine ⟨10533391345024111341932449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14044521793365481789243265 10533391345024111341932449)
          ·
            refine ⟨7900043508768083506449337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533391345024111341932449 7900043508768083506449337)
            ·
              refine ⟨5925032631576062629837003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900043508768083506449337 5925032631576062629837003)
              ·
                refine ⟨8887548947364093944755505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925032631576062629837003 8887548947364093944755505)
                ·
                  refine ⟨6665661710523070458566629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887548947364093944755505 6665661710523070458566629)
                  ·
                    refine ⟨1249811570723075710981243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665661710523070458566629 1249811570723075710981243)
                    ·
                      rfl

theorem cell23_7301998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7301998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7301998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7301998 prefixEnd_7301998 := by exact prefixLift 7301998
  have htrace : WordTrace (prefixWord ++ tailWord_7301998) baseStart_7301998 baseEnd_7301998 := by
    simpa [prefixWord, tailWord_7301998, baseEnd_7301998] using wordTrace_append hprefix tailTrace_7301998
  have hstable : (prefixWord ++ tailWord_7301998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7301998).length < 2 ^ (prefixWord ++ tailWord_7301998).sum := by decide
  have hdescent : baseEnd_7301998 < baseStart_7301998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7301998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302020 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_7302020 : Nat := 118140960795 + 7302020 * 2 ^ 59
def prefixEnd_7302020 : Nat := 4983230072969 + 3 ^ 40 * 7302020 * 2
def baseEnd_7302020 : Nat := 1249815336247875348956209

theorem tailTrace_7302020 : CollatzResearch.WordTrace tailWord_7302020 prefixEnd_7302020 1249815336247875348956209 := by
  unfold tailWord_7302020
  simp only [CollatzResearch.WordTrace]
  refine ⟨133163274503018050287771757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177551032670690733717029009 133163274503018050287771757)
  ·
    refine ⟨49936227938631768857914409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133163274503018050287771757 49936227938631768857914409)
    ·
      refine ⟨37452170953973826643435807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49936227938631768857914409 37452170953973826643435807)
      ·
        refine ⟨56178256430960739965153711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37452170953973826643435807 56178256430960739965153711)
        ·
          refine ⟨84267384646441109947730567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56178256430960739965153711 84267384646441109947730567)
          ·
            refine ⟨126401076969661664921595851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84267384646441109947730567 126401076969661664921595851)
            ·
              refine ⟨189601615454492497382393777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126401076969661664921595851 189601615454492497382393777)
              ·
                refine ⟨142201211590869373036795333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189601615454492497382393777 142201211590869373036795333)
                ·
                  refine ⟨26662727173288007444399125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142201211590869373036795333 26662727173288007444399125)
                  ·
                    refine ⟨1249815336247875348956209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26662727173288007444399125 1249815336247875348956209)
                    ·
                      rfl

theorem cell23_7302020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_7302020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302020 prefixEnd_7302020 := by exact prefixLift 7302020
  have htrace : WordTrace (prefixWord ++ tailWord_7302020) baseStart_7302020 baseEnd_7302020 := by
    simpa [prefixWord, tailWord_7302020, baseEnd_7302020] using wordTrace_append hprefix tailTrace_7302020
  have hstable : (prefixWord ++ tailWord_7302020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302020).length < 2 ^ (prefixWord ++ tailWord_7302020).sum := by decide
  have hdescent : baseEnd_7302020 < baseStart_7302020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302027 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 3, 4, 2]
def baseStart_7302027 : Nat := 118140960795 + 7302027 * 2 ^ 59
def prefixEnd_7302027 : Nat := 4983230072969 + 3 ^ 40 * 7302027 * 2
def baseEnd_7302027 : Nat := 3749449603108207519481095

theorem tailTrace_7302027 : CollatzResearch.WordTrace tailWord_7302027 prefixEnd_7302027 3749449603108207519481095 := by
  unfold tailWord_7302027
  simp only [CollatzResearch.WordTrace]
  refine ⟨266326804317010740771048335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177551202878007160514032223 266326804317010740771048335)
  ·
    refine ⟨399490206475516111156572503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266326804317010740771048335 399490206475516111156572503)
    ·
      refine ⟨599235309713274166734858755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399490206475516111156572503 599235309713274166734858755)
      ·
        refine ⟨898852964569911250102288133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599235309713274166734858755 898852964569911250102288133)
        ·
          refine ⟨168534930856858359394179025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 898852964569911250102288133 168534930856858359394179025)
          ·
            refine ⟨126401198142643769545634269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168534930856858359394179025 126401198142643769545634269)
            ·
              refine ⟨47400449303491413579612851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126401198142643769545634269 47400449303491413579612851)
              ·
                refine ⟨71100673955237120369419277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47400449303491413579612851 71100673955237120369419277)
                ·
                  refine ⟨26662752733213920138532229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71100673955237120369419277 26662752733213920138532229)
                  ·
                    refine ⟨4999266137477610025974793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26662752733213920138532229 4999266137477610025974793)
                    ·
                      refine ⟨3749449603108207519481095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999266137477610025974793 3749449603108207519481095)
                      ·
                        rfl

theorem cell23_7302027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4, 2].length) (baseStart_7302027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302027 prefixEnd_7302027 := by exact prefixLift 7302027
  have htrace : WordTrace (prefixWord ++ tailWord_7302027) baseStart_7302027 baseEnd_7302027 := by
    simpa [prefixWord, tailWord_7302027, baseEnd_7302027] using wordTrace_append hprefix tailTrace_7302027
  have hstable : (prefixWord ++ tailWord_7302027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302027).length < 2 ^ (prefixWord ++ tailWord_7302027).sum := by decide
  have hdescent : baseEnd_7302027 < baseStart_7302027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302047 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7302047 : Nat := 118140960795 + 7302047 * 2 ^ 59
def prefixEnd_7302047 : Nat := 4983230072969 + 3 ^ 40 * 7302047 * 2
def baseEnd_7302047 : Nat := 3749459872721297441231003

theorem tailTrace_7302047 : CollatzResearch.WordTrace tailWord_7302047 prefixEnd_7302047 3749459872721297441231003 := by
  unfold tailWord_7302047
  simp only [CollatzResearch.WordTrace]
  refine ⟨266327533776938284186776395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177551689184625522791184263 266327533776938284186776395)
  ·
    refine ⟨399491300665407426280164593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266327533776938284186776395 399491300665407426280164593)
    ·
      refine ⟨299618475499055569710123445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399491300665407426280164593 299618475499055569710123445)
      ·
        refine ⟨28089232078036459660324073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299618475499055569710123445 28089232078036459660324073)
        ·
          refine ⟨21066924058527344745243055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28089232078036459660324073 21066924058527344745243055)
          ·
            refine ⟨31600386087791017117864583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21066924058527344745243055 31600386087791017117864583)
            ·
              refine ⟨47400579131686525676796875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31600386087791017117864583 47400579131686525676796875)
              ·
                refine ⟨71100868697529788515195313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47400579131686525676796875 71100868697529788515195313)
                ·
                  refine ⟨53325651523147341386396485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71100868697529788515195313 53325651523147341386396485)
                  ·
                    refine ⟨9998559660590126509949341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53325651523147341386396485 9998559660590126509949341)
                    ·
                      refine ⟨3749459872721297441231003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998559660590126509949341 3749459872721297441231003)
                      ·
                        rfl

theorem cell23_7302047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7302047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302047 prefixEnd_7302047 := by exact prefixLift 7302047
  have htrace : WordTrace (prefixWord ++ tailWord_7302047) baseStart_7302047 baseEnd_7302047 := by
    simpa [prefixWord, tailWord_7302047, baseEnd_7302047] using wordTrace_append hprefix tailTrace_7302047
  have hstable : (prefixWord ++ tailWord_7302047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302047).length < 2 ^ (prefixWord ++ tailWord_7302047).sum := by decide
  have hdescent : baseEnd_7302047 < baseStart_7302047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302114 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7302114 : Nat := 118140960795 + 7302114 * 2 ^ 59
def prefixEnd_7302114 : Nat := 4983230072969 + 3 ^ 40 * 7302114 * 2
def baseEnd_7302114 : Nat := 1249831425308382893031065

theorem tailTrace_7302114 : CollatzResearch.WordTrace tailWord_7302114 prefixEnd_7302114 1249831425308382893031065 := by
  unfold tailWord_7302114
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582494366923888657366349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177553318311797036419643597 66582494366923888657366349)
  ·
    refine ⟨24968435387596458246512381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66582494366923888657366349 24968435387596458246512381)
    ·
      refine ⟨9363163270348671842442143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24968435387596458246512381 9363163270348671842442143)
      ·
        refine ⟨14044744905523007763663215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9363163270348671842442143 14044744905523007763663215)
        ·
          refine ⟨21067117358284511645494823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044744905523007763663215 21067117358284511645494823)
          ·
            refine ⟨31600676037426767468242235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21067117358284511645494823 31600676037426767468242235)
            ·
              refine ⟨47401014056140151202363353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31600676037426767468242235 47401014056140151202363353)
              ·
                refine ⟨35550760542105113401772515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47401014056140151202363353 35550760542105113401772515)
                ·
                  refine ⟨53326140813157670102658773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35550760542105113401772515 53326140813157670102658773)
                  ·
                    refine ⟨1249831425308382893031065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53326140813157670102658773 1249831425308382893031065)
                    ·
                      rfl

theorem cell23_7302114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7302114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302114 prefixEnd_7302114 := by exact prefixLift 7302114
  have htrace : WordTrace (prefixWord ++ tailWord_7302114) baseStart_7302114 baseEnd_7302114 := by
    simpa [prefixWord, tailWord_7302114, baseEnd_7302114] using wordTrace_append hprefix tailTrace_7302114
  have hstable : (prefixWord ++ tailWord_7302114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302114).length < 2 ^ (prefixWord ++ tailWord_7302114).sum := by decide
  have hdescent : baseEnd_7302114 < baseStart_7302114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302134 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7302134 : Nat := 118140960795 + 7302134 * 2 ^ 59
def prefixEnd_7302134 : Nat := 4983230072969 + 3 ^ 40 * 7302134 * 2
def baseEnd_7302134 : Nat := 3749504545538238600843103

theorem tailTrace_7302134 : CollatzResearch.WordTrace tailWord_7302134 prefixEnd_7302134 3749504545538238600843103 := by
  unfold tailWord_7302134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645669182976443627824591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177553804618415398696795637 16645669182976443627824591)
  ·
    refine ⟨24968503774464665441736887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16645669182976443627824591 24968503774464665441736887)
    ·
      refine ⟨37452755661696998162605331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24968503774464665441736887 37452755661696998162605331)
      ·
        refine ⟨56179133492545497243907997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37452755661696998162605331 56179133492545497243907997)
        ·
          refine ⟨21067175059704561466465499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56179133492545497243907997 21067175059704561466465499)
          ·
            refine ⟨31600762589556842199698249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21067175059704561466465499 31600762589556842199698249)
            ·
              refine ⟨23700571942167631649773687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31600762589556842199698249 23700571942167631649773687)
              ·
                refine ⟨35550857913251447474660531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23700571942167631649773687 35550857913251447474660531)
                ·
                  refine ⟨53326286869877171211990797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35550857913251447474660531 53326286869877171211990797)
                  ·
                    refine ⟨19997357576203939204496549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53326286869877171211990797 19997357576203939204496549)
                    ·
                      refine ⟨3749504545538238600843103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19997357576203939204496549 3749504545538238600843103)
                      ·
                        rfl

theorem cell23_7302134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7302134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302134 prefixEnd_7302134 := by exact prefixLift 7302134
  have htrace : WordTrace (prefixWord ++ tailWord_7302134) baseStart_7302134 baseEnd_7302134 := by
    simpa [prefixWord, tailWord_7302134, baseEnd_7302134] using wordTrace_append hprefix tailTrace_7302134
  have hstable : (prefixWord ++ tailWord_7302134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302134).length < 2 ^ (prefixWord ++ tailWord_7302134).sum := by decide
  have hdescent : baseEnd_7302134 < baseStart_7302134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302137 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_7302137 : Nat := 118140960795 + 7302137 * 2 ^ 59
def prefixEnd_7302137 : Nat := 4983230072969 + 3 ^ 40 * 7302137 * 2
def baseEnd_7302137 : Nat := 3749506085980202089105589

theorem tailTrace_7302137 : CollatzResearch.WordTrace tailWord_7302137 prefixEnd_7302137 3749506085980202089105589 := by
  unfold tailWord_7302137
  simp only [CollatzResearch.WordTrace]
  refine ⟨266330816346612229557552665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177553877564408153038368443 266330816346612229557552665)
  ·
    refine ⟨199748112259959172168164499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266330816346612229557552665 199748112259959172168164499)
    ·
      refine ⟨299622168389938758252246749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199748112259959172168164499 299622168389938758252246749)
      ·
        refine ⟨112358313146227034344592531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299622168389938758252246749 112358313146227034344592531)
        ·
          refine ⟨168537469719340551516888797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112358313146227034344592531 168537469719340551516888797)
          ·
            refine ⟨63201551144752706818833299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168537469719340551516888797 63201551144752706818833299)
            ·
              refine ⟨94802326717129060228249949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63201551144752706818833299 94802326717129060228249949)
              ·
                refine ⟨35550872518923397585593731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94802326717129060228249949 35550872518923397585593731)
                ·
                  refine ⟨53326308778385096378390597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35550872518923397585593731 53326308778385096378390597)
                  ·
                    refine ⟨9998682895947205570948237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53326308778385096378390597 9998682895947205570948237)
                    ·
                      refine ⟨3749506085980202089105589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998682895947205570948237 3749506085980202089105589)
                      ·
                        rfl

theorem cell23_7302137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_7302137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302137 prefixEnd_7302137 := by exact prefixLift 7302137
  have htrace : WordTrace (prefixWord ++ tailWord_7302137) baseStart_7302137 baseEnd_7302137 := by
    simpa [prefixWord, tailWord_7302137, baseEnd_7302137] using wordTrace_append hprefix tailTrace_7302137
  have hstable : (prefixWord ++ tailWord_7302137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302137).length < 2 ^ (prefixWord ++ tailWord_7302137).sum := by decide
  have hdescent : baseEnd_7302137 < baseStart_7302137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302154 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_7302154 : Nat := 118140960795 + 7302154 * 2 ^ 59
def prefixEnd_7302154 : Nat := 4983230072969 + 3 ^ 40 * 7302154 * 2
def baseEnd_7302154 : Nat := 3749514815151328522593011

theorem tailTrace_7302154 : CollatzResearch.WordTrace tailWord_7302154 prefixEnd_7302154 3749514815151328522593011 := by
  unfold tailWord_7302154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582859096887660365230379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177554290925033760973947677 66582859096887660365230379)
  ·
    refine ⟨99874288645331490547845569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66582859096887660365230379 99874288645331490547845569)
    ·
      refine ⟨74905716483998617910884177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99874288645331490547845569 74905716483998617910884177)
      ·
        refine ⟨56179287362998963433163133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74905716483998617910884177 56179287362998963433163133)
        ·
          refine ⟨21067232761124611287436175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56179287362998963433163133 21067232761124611287436175)
          ·
            refine ⟨31600849141686916931154263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21067232761124611287436175 31600849141686916931154263)
            ·
              refine ⟨47401273712530375396731395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31600849141686916931154263 47401273712530375396731395)
              ·
                refine ⟨71101910568795563095097093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47401273712530375396731395 71101910568795563095097093)
                ·
                  refine ⟨13331608231649168080330705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71101910568795563095097093 13331608231649168080330705)
                  ·
                    refine ⟨9998706173736876060248029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13331608231649168080330705 9998706173736876060248029)
                    ·
                      refine ⟨3749514815151328522593011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998706173736876060248029 3749514815151328522593011)
                      ·
                        rfl

theorem cell23_7302154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_7302154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302154 prefixEnd_7302154 := by exact prefixLift 7302154
  have htrace : WordTrace (prefixWord ++ tailWord_7302154) baseStart_7302154 baseEnd_7302154 := by
    simpa [prefixWord, tailWord_7302154, baseEnd_7302154] using wordTrace_append hprefix tailTrace_7302154
  have hstable : (prefixWord ++ tailWord_7302154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302154).length < 2 ^ (prefixWord ++ tailWord_7302154).sum := by decide
  have hdescent : baseEnd_7302154 < baseStart_7302154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302187 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 3, 5]
def baseStart_7302187 : Nat := 118140960795 + 7302187 * 2 ^ 59
def prefixEnd_7302187 : Nat := 4983230072969 + 3 ^ 40 * 7302187 * 2
def baseEnd_7302187 : Nat := 1249843920004308964493453

theorem tailTrace_7302187 : CollatzResearch.WordTrace tailWord_7302187 prefixEnd_7302187 1249843920004308964493453 := by
  unfold tailWord_7302187
  simp only [CollatzResearch.WordTrace]
  refine ⟨266332639996431088096872815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177555093330954058731248543 266332639996431088096872815)
  ·
    refine ⟨399498959994646632145309223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266332639996431088096872815 399498959994646632145309223)
    ·
      refine ⟨599248439991969948217963835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399498959994646632145309223 599248439991969948217963835)
      ·
        refine ⟨898872659987954922326945753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599248439991969948217963835 898872659987954922326945753)
        ·
          refine ⟨674154494990966191745209315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898872659987954922326945753 674154494990966191745209315)
          ·
            refine ⟨1011231742486449287617813973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674154494990966191745209315 1011231742486449287617813973)
            ·
              refine ⟨23700743964526155178542515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1011231742486449287617813973 23700743964526155178542515)
              ·
                refine ⟨35551115946789232767813773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23700743964526155178542515 35551115946789232767813773)
                ·
                  refine ⟨13331668480045962287930165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35551115946789232767813773 13331668480045962287930165)
                  ·
                    refine ⟨1249843920004308964493453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13331668480045962287930165 1249843920004308964493453)
                    ·
                      rfl

theorem cell23_7302187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 5].length) (baseStart_7302187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302187 prefixEnd_7302187 := by exact prefixLift 7302187
  have htrace : WordTrace (prefixWord ++ tailWord_7302187) baseStart_7302187 baseEnd_7302187 := by
    simpa [prefixWord, tailWord_7302187, baseEnd_7302187] using wordTrace_append hprefix tailTrace_7302187
  have hstable : (prefixWord ++ tailWord_7302187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302187).length < 2 ^ (prefixWord ++ tailWord_7302187).sum := by decide
  have hdescent : baseEnd_7302187 < baseStart_7302187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302227 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3]
def baseStart_7302227 : Nat := 118140960795 + 7302227 * 2 ^ 59
def prefixEnd_7302227 : Nat := 4983230072969 + 3 ^ 40 * 7302227 * 2
def baseEnd_7302227 : Nat := 3749552299239106736980175

theorem tailTrace_7302227 : CollatzResearch.WordTrace tailWord_7302227 prefixEnd_7302227 3749552299239106736980175 := by
  unfold tailWord_7302227
  simp only [CollatzResearch.WordTrace]
  refine ⟨266334098916286174928328935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177556065944190783285552623 266334098916286174928328935)
  ·
    refine ⟨399501148374429262392493403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266334098916286174928328935 399501148374429262392493403)
    ·
      refine ⟨599251722561643893588740105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399501148374429262392493403 599251722561643893588740105)
      ·
        refine ⟨449438791921232920191555079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599251722561643893588740105 449438791921232920191555079)
        ·
          refine ⟨674158187881849380287332619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449438791921232920191555079 674158187881849380287332619)
          ·
            refine ⟨1011237281822774070430998929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674158187881849380287332619 1011237281822774070430998929)
            ·
              refine ⟨758427961367080552823249197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011237281822774070430998929 758427961367080552823249197)
              ·
                refine ⟨284410485512655207308718449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758427961367080552823249197 284410485512655207308718449)
                ·
                  refine ⟨213307864134491405481538837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284410485512655207308718449 213307864134491405481538837)
                  ·
                    refine ⟨9998806131304284631947133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213307864134491405481538837 9998806131304284631947133)
                    ·
                      refine ⟨3749552299239106736980175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998806131304284631947133 3749552299239106736980175)
                      ·
                        rfl

theorem cell23_7302227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_7302227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302227 prefixEnd_7302227 := by exact prefixLift 7302227
  have htrace : WordTrace (prefixWord ++ tailWord_7302227) baseStart_7302227 baseEnd_7302227 := by
    simpa [prefixWord, tailWord_7302227, baseEnd_7302227] using wordTrace_append hprefix tailTrace_7302227
  have hstable : (prefixWord ++ tailWord_7302227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302227).length < 2 ^ (prefixWord ++ tailWord_7302227).sum := by decide
  have hdescent : baseEnd_7302227 < baseStart_7302227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302238 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7302238 : Nat := 118140960795 + 7302238 * 2 ^ 59
def prefixEnd_7302238 : Nat := 4983230072969 + 3 ^ 40 * 7302238 * 2
def baseEnd_7302238 : Nat := 1249852649175435397980875

theorem tailTrace_7302238 : CollatzResearch.WordTrace tailWord_7302238 prefixEnd_7302238 1249852649175435397980875 := by
  unfold tailWord_7302238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33291812514905790475872421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177556333412830882537986245 33291812514905790475872421)
  ·
    refine ⟨6242214846544835714226079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33291812514905790475872421 6242214846544835714226079)
    ·
      refine ⟨9363322269817253571339119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242214846544835714226079 9363322269817253571339119)
      ·
        refine ⟨14044983404725880357008679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9363322269817253571339119 14044983404725880357008679)
        ·
          refine ⟨21067475107088820535513019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044983404725880357008679 21067475107088820535513019)
          ·
            refine ⟨31601212660633230803269529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21067475107088820535513019 31601212660633230803269529)
            ·
              refine ⟨23700909495474923102452147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31601212660633230803269529 23700909495474923102452147)
              ·
                refine ⟨35551364243212384653678221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23700909495474923102452147 35551364243212384653678221)
                ·
                  refine ⟨13331761591204644245129333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35551364243212384653678221 13331761591204644245129333)
                  ·
                    refine ⟨1249852649175435397980875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13331761591204644245129333 1249852649175435397980875)
                    ·
                      rfl

theorem cell23_7302238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7302238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302238 prefixEnd_7302238 := by exact prefixLift 7302238
  have htrace : WordTrace (prefixWord ++ tailWord_7302238) baseStart_7302238 baseEnd_7302238 := by
    simpa [prefixWord, tailWord_7302238, baseEnd_7302238] using wordTrace_append hprefix tailTrace_7302238
  have hstable : (prefixWord ++ tailWord_7302238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302238).length < 2 ^ (prefixWord ++ tailWord_7302238).sum := by decide
  have hdescent : baseEnd_7302238 < baseStart_7302238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302241 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_7302241 : Nat := 118140960795 + 7302241 * 2 ^ 59
def prefixEnd_7302241 : Nat := 4983230072969 + 3 ^ 40 * 7302241 * 2
def baseEnd_7302241 : Nat := 3749559487968269682205111

theorem tailTrace_7302241 : CollatzResearch.WordTrace tailWord_7302241 prefixEnd_7302241 3749559487968269682205111 := by
  unfold tailWord_7302241
  simp only [CollatzResearch.WordTrace]
  refine ⟨266334609538235455319338577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177556406358823636879559051 266334609538235455319338577)
  ·
    refine ⟨199750957153676591489503933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266334609538235455319338577 199750957153676591489503933)
    ·
      refine ⟨74906608932628721808563975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199750957153676591489503933 74906608932628721808563975)
      ·
        refine ⟨112359913398943082712845963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74906608932628721808563975 112359913398943082712845963)
        ·
          refine ⟨168539870098414624069268945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112359913398943082712845963 168539870098414624069268945)
          ·
            refine ⟨126404902573810968051951709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168539870098414624069268945 126404902573810968051951709)
            ·
              refine ⟨47401838465179113019481891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126404902573810968051951709 47401838465179113019481891)
              ·
                refine ⟨71102757697768669529222837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47401838465179113019481891 71102757697768669529222837)
                ·
                  refine ⟨6665883534165812768364641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71102757697768669529222837 6665883534165812768364641)
                  ·
                    refine ⟨4999412650624359576273481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665883534165812768364641 4999412650624359576273481)
                    ·
                      refine ⟨3749559487968269682205111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999412650624359576273481 3749559487968269682205111)
                      ·
                        rfl

theorem cell23_7302241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_7302241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302241 prefixEnd_7302241 := by exact prefixLift 7302241
  have htrace : WordTrace (prefixWord ++ tailWord_7302241) baseStart_7302241 baseEnd_7302241 := by
    simpa [prefixWord, tailWord_7302241, baseEnd_7302241] using wordTrace_append hprefix tailTrace_7302241
  have hstable : (prefixWord ++ tailWord_7302241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302241).length < 2 ^ (prefixWord ++ tailWord_7302241).sum := by decide
  have hdescent : baseEnd_7302241 < baseStart_7302241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302291 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 3]
def baseStart_7302291 : Nat := 118140960795 + 7302291 * 2 ^ 59
def prefixEnd_7302291 : Nat := 4983230072969 + 3 ^ 40 * 7302291 * 2
def baseEnd_7302291 : Nat := 3749585162000994486579881

theorem tailTrace_7302291 : CollatzResearch.WordTrace tailWord_7302291 prefixEnd_7302291 3749585162000994486579881 := by
  unfold tailWord_7302291
  simp only [CollatzResearch.WordTrace]
  refine ⟨266336433188054313858658727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177557622125369542572439151 266336433188054313858658727)
  ·
    refine ⟨399504649782081470787988091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266336433188054313858658727 399504649782081470787988091)
    ·
      refine ⟨599256974673122206181982137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399504649782081470787988091 599256974673122206181982137)
      ·
        refine ⟨449442731004841654636486603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599256974673122206181982137 449442731004841654636486603)
        ·
          refine ⟨674164096507262481954729905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449442731004841654636486603 674164096507262481954729905)
          ·
            refine ⟨505623072380446861466047429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674164096507262481954729905 505623072380446861466047429)
            ·
              refine ⟨94804326071333786524883893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 505623072380446861466047429 94804326071333786524883893)
              ·
                refine ⟨8887905569187542486707865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94804326071333786524883893 8887905569187542486707865)
                ·
                  refine ⟨6665929176890656865030899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887905569187542486707865 6665929176890656865030899)
                  ·
                    refine ⟨9998893765335985297546349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665929176890656865030899 9998893765335985297546349)
                    ·
                      refine ⟨3749585162000994486579881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9998893765335985297546349 3749585162000994486579881)
                      ·
                        rfl

theorem cell23_7302291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_7302291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302291 prefixEnd_7302291 := by exact prefixLift 7302291
  have htrace : WordTrace (prefixWord ++ tailWord_7302291) baseStart_7302291 baseEnd_7302291 := by
    simpa [prefixWord, tailWord_7302291, baseEnd_7302291] using wordTrace_append hprefix tailTrace_7302291
  have hstable : (prefixWord ++ tailWord_7302291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302291).length < 2 ^ (prefixWord ++ tailWord_7302291).sum := by decide
  have hdescent : baseEnd_7302291 < baseStart_7302291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302307 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 8]
def baseStart_7302307 : Nat := 118140960795 + 7302307 * 2 ^ 59
def prefixEnd_7302307 : Nat := 4983230072969 + 3 ^ 40 * 7302307 * 2
def baseEnd_7302307 : Nat := 1249864459230488807993269

theorem tailTrace_7302307 : CollatzResearch.WordTrace tailWord_7302307 prefixEnd_7302307 1249864459230488807993269 := by
  unfold tailWord_7302307
  simp only [CollatzResearch.WordTrace]
  refine ⟨266337016755996348591241175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177558011170664232394160783 266337016755996348591241175)
  ·
    refine ⟨399505525133994522886861763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266337016755996348591241175 399505525133994522886861763)
    ·
      refine ⟨599258287700991784330292645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399505525133994522886861763 599258287700991784330292645)
      ·
        refine ⟨112360928943935959561929871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599258287700991784330292645 112360928943935959561929871)
        ·
          refine ⟨168541393415903939342894807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112360928943935959561929871 168541393415903939342894807)
          ·
            refine ⟨252812090123855909014342211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168541393415903939342894807 252812090123855909014342211)
            ·
              refine ⟨379218135185783863521513317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252812090123855909014342211 379218135185783863521513317)
              ·
                refine ⟨71103400347334474410283747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379218135185783863521513317 71103400347334474410283747)
                ·
                  refine ⟨106655100521001711615425621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71103400347334474410283747 106655100521001711615425621)
                  ·
                    refine ⟨1249864459230488807993269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106655100521001711615425621 1249864459230488807993269)
                    ·
                      rfl

theorem cell23_7302307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_7302307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302307 prefixEnd_7302307 := by exact prefixLift 7302307
  have htrace : WordTrace (prefixWord ++ tailWord_7302307) baseStart_7302307 baseEnd_7302307 := by
    simpa [prefixWord, tailWord_7302307, baseEnd_7302307] using wordTrace_append hprefix tailTrace_7302307
  have hstable : (prefixWord ++ tailWord_7302307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302307).length < 2 ^ (prefixWord ++ tailWord_7302307).sum := by decide
  have hdescent : baseEnd_7302307 < baseStart_7302307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302326 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7302326 : Nat := 118140960795 + 7302326 * 2 ^ 59
def prefixEnd_7302326 : Nat := 4983230072969 + 3 ^ 40 * 7302326 * 2
def baseEnd_7302326 : Nat := 3749603133823901849642221

theorem tailTrace_7302326 : CollatzResearch.WordTrace tailWord_7302326 prefixEnd_7302326 3749603133823901849642221 := by
  unfold tailWord_7302326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646106858932969677261427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177558473161951676557455221 16646106858932969677261427)
  ·
    refine ⟨24969160288399454515892141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16646106858932969677261427 24969160288399454515892141)
    ·
      refine ⟨9363435108149795443459553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24969160288399454515892141 9363435108149795443459553)
      ·
        refine ⟨7022576331112346582594665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9363435108149795443459553 7022576331112346582594665)
        ·
          refine ⟨5266932248334259936945999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7022576331112346582594665 5266932248334259936945999)
          ·
            refine ⟨7900398372501389905418999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266932248334259936945999 7900398372501389905418999)
            ·
              refine ⟨11850597558752084858128499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900398372501389905418999 11850597558752084858128499)
              ·
                refine ⟨17775896338128127287192749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11850597558752084858128499 17775896338128127287192749)
                ·
                  refine ⟨6665961126798047732697281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17775896338128127287192749 6665961126798047732697281)
                  ·
                    refine ⟨4999470845098535799522961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665961126798047732697281 4999470845098535799522961)
                    ·
                      refine ⟨3749603133823901849642221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999470845098535799522961 3749603133823901849642221)
                      ·
                        rfl

theorem cell23_7302326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7302326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302326 prefixEnd_7302326 := by exact prefixLift 7302326
  have htrace : WordTrace (prefixWord ++ tailWord_7302326) baseStart_7302326 baseEnd_7302326 := by
    simpa [prefixWord, tailWord_7302326, baseEnd_7302326] using wordTrace_append hprefix tailTrace_7302326
  have hstable : (prefixWord ++ tailWord_7302326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302326).length < 2 ^ (prefixWord ++ tailWord_7302326).sum := by decide
  have hdescent : baseEnd_7302326 < baseStart_7302326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302344 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7302344 : Nat := 118140960795 + 7302344 * 2 ^ 59
def prefixEnd_7302344 : Nat := 4983230072969 + 3 ^ 40 * 7302344 * 2
def baseEnd_7302344 : Nat := 3749612376475682779217137

theorem tailTrace_7302344 : CollatzResearch.WordTrace tailWord_7302344 prefixEnd_7302344 3749612376475682779217137 := by
  unfold tailWord_7302344
  simp only [CollatzResearch.WordTrace]
  refine ⟨133169183128431151955169043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177558910837908202606892057 133169183128431151955169043)
  ·
    refine ⟨199753774692646727932753565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133169183128431151955169043 199753774692646727932753565)
    ·
      refine ⟨74907665509742522974782587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199753774692646727932753565 74907665509742522974782587)
      ·
        refine ⟨112361498264613784462173881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74907665509742522974782587 112361498264613784462173881)
        ·
          refine ⟨84271123698460338346630411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112361498264613784462173881 84271123698460338346630411)
          ·
            refine ⟨126406685547690507519945617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84271123698460338346630411 126406685547690507519945617)
            ·
              refine ⟨94805014160767880639959213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126406685547690507519945617 94805014160767880639959213)
              ·
                refine ⟨35551880310287955239984705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94805014160767880639959213 35551880310287955239984705)
                ·
                  refine ⟨26663910232715966429988529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35551880310287955239984705 26663910232715966429988529)
                  ·
                    refine ⟨19997932674536974822491397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26663910232715966429988529 19997932674536974822491397)
                    ·
                      refine ⟨3749612376475682779217137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19997932674536974822491397 3749612376475682779217137)
                      ·
                        rfl

theorem cell23_7302344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7302344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302344 prefixEnd_7302344 := by exact prefixLift 7302344
  have htrace : WordTrace (prefixWord ++ tailWord_7302344) baseStart_7302344 baseEnd_7302344 := by
    simpa [prefixWord, tailWord_7302344, baseEnd_7302344] using wordTrace_append hprefix tailTrace_7302344
  have hstable : (prefixWord ++ tailWord_7302344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302344).length < 2 ^ (prefixWord ++ tailWord_7302344).sum := by decide
  have hdescent : baseEnd_7302344 < baseStart_7302344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302354 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_7302354 : Nat := 118140960795 + 7302354 * 2 ^ 59
def prefixEnd_7302354 : Nat := 4983230072969 + 3 ^ 40 * 7302354 * 2
def baseEnd_7302354 : Nat := 416624167920247526676899

theorem tailTrace_7302354 : CollatzResearch.WordTrace tailWord_7302354 prefixEnd_7302354 416624167920247526676899 := by
  unfold tailWord_7302354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66584682746706518904550529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177559153991217383745468077 66584682746706518904550529)
  ·
    refine ⟨49938512060029889178412897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66584682746706518904550529 49938512060029889178412897)
    ·
      refine ⟨37453884045022416883809673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49938512060029889178412897 37453884045022416883809673)
      ·
        refine ⟨28090413033766812662857255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37453884045022416883809673 28090413033766812662857255)
        ·
          refine ⟨42135619550650218994285883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28090413033766812662857255 42135619550650218994285883)
          ·
            refine ⟨63203429325975328491428825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42135619550650218994285883 63203429325975328491428825)
            ·
              refine ⟨47402571994481496368571619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63203429325975328491428825 47402571994481496368571619)
              ·
                refine ⟨71103857991722244552857429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47402571994481496368571619 71103857991722244552857429)
                ·
                  refine ⟨416624167920247526676899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71103857991722244552857429 416624167920247526676899)
                  ·
                    rfl

theorem cell23_7302354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_7302354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302354 prefixEnd_7302354 := by exact prefixLift 7302354
  have htrace : WordTrace (prefixWord ++ tailWord_7302354) baseStart_7302354 baseEnd_7302354 := by
    simpa [prefixWord, tailWord_7302354, baseEnd_7302354] using wordTrace_append hprefix tailTrace_7302354
  have hstable : (prefixWord ++ tailWord_7302354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302354).length < 2 ^ (prefixWord ++ tailWord_7302354).sum := by decide
  have hdescent : baseEnd_7302354 < baseStart_7302354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302365 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7302365 : Nat := 118140960795 + 7302365 * 2 ^ 59
def prefixEnd_7302365 : Nat := 4983230072969 + 3 ^ 40 * 7302365 * 2
def baseEnd_7302365 : Nat := 3749623159569427197054541

theorem tailTrace_7302365 : CollatzResearch.WordTrace tailWord_7302365 prefixEnd_7302365 3749623159569427197054541 := by
  unfold tailWord_7302365
  simp only [CollatzResearch.WordTrace]
  refine ⟨266339132189786224496852549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177559421459857482997901699 266339132189786224496852549)
  ·
    refine ⟨49938587285584917093159853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266339132189786224496852549 49938587285584917093159853)
    ·
      refine ⟨18726970232094343909934945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49938587285584917093159853 18726970232094343909934945)
      ·
        refine ⟨14045227674070757932451209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18726970232094343909934945 14045227674070757932451209)
        ·
          refine ⟨10533920755553068449338407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14045227674070757932451209 10533920755553068449338407)
          ·
            refine ⟨15800881133329602674007611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10533920755553068449338407 15800881133329602674007611)
            ·
              refine ⟨23701321699994404011011417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15800881133329602674007611 23701321699994404011011417)
              ·
                refine ⟨17775991274995803008258563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23701321699994404011011417 17775991274995803008258563)
                ·
                  refine ⟨26663986912493704512387845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17775991274995803008258563 26663986912493704512387845)
                  ·
                    refine ⟨4999497546092569596072721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26663986912493704512387845 4999497546092569596072721)
                    ·
                      refine ⟨3749623159569427197054541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999497546092569596072721 3749623159569427197054541)
                      ·
                        rfl

theorem cell23_7302365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7302365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302365 prefixEnd_7302365 := by exact prefixLift 7302365
  have htrace : WordTrace (prefixWord ++ tailWord_7302365) baseStart_7302365 baseEnd_7302365 := by
    simpa [prefixWord, tailWord_7302365, baseEnd_7302365] using wordTrace_append hprefix tailTrace_7302365
  have hstable : (prefixWord ++ tailWord_7302365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302365).length < 2 ^ (prefixWord ++ tailWord_7302365).sum := by decide
  have hdescent : baseEnd_7302365 < baseStart_7302365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302394 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_7302394 : Nat := 118140960795 + 7302394 * 2 ^ 59
def prefixEnd_7302394 : Nat := 4983230072969 + 3 ^ 40 * 7302394 * 2
def baseEnd_7302394 : Nat := 3749638050508407583591907

theorem tailTrace_7302394 : CollatzResearch.WordTrace tailWord_7302394 prefixEnd_7302394 3749638050508407583591907 := by
  unfold tailWord_7302394
  simp only [CollatzResearch.WordTrace]
  refine ⟨66585047476670290612414559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177560126604454108299772157 66585047476670290612414559)
  ·
    refine ⟨99877571215005435918621839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66585047476670290612414559 99877571215005435918621839)
    ·
      refine ⟨149816356822508153877932759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99877571215005435918621839 149816356822508153877932759)
      ·
        refine ⟨224724535233762230816899139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149816356822508153877932759 224724535233762230816899139)
        ·
          refine ⟨337086802850643346225348709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224724535233762230816899139 337086802850643346225348709)
          ·
            refine ⟨63203775534495627417252883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337086802850643346225348709 63203775534495627417252883)
            ·
              refine ⟨94805663301743441125879325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63203775534495627417252883 94805663301743441125879325)
              ·
                refine ⟨35552123738153790422204747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94805663301743441125879325 35552123738153790422204747)
                ·
                  refine ⟨53328185607230685633307121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35552123738153790422204747 53328185607230685633307121)
                  ·
                    refine ⟨39996139205423014224980341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53328185607230685633307121 39996139205423014224980341)
                    ·
                      refine ⟨3749638050508407583591907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39996139205423014224980341 3749638050508407583591907)
                      ·
                        rfl

theorem cell23_7302394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_7302394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302394 prefixEnd_7302394 := by exact prefixLift 7302394
  have htrace : WordTrace (prefixWord ++ tailWord_7302394) baseStart_7302394 baseEnd_7302394 := by
    simpa [prefixWord, tailWord_7302394, baseEnd_7302394] using wordTrace_append hprefix tailTrace_7302394
  have hstable : (prefixWord ++ tailWord_7302394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302394).length < 2 ^ (prefixWord ++ tailWord_7302394).sum := by decide
  have hdescent : baseEnd_7302394 < baseStart_7302394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302398 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_7302398 : Nat := 118140960795 + 7302398 * 2 ^ 59
def prefixEnd_7302398 : Nat := 4983230072969 + 3 ^ 40 * 7302398 * 2
def baseEnd_7302398 : Nat := 3749640104431025567941889

theorem tailTrace_7302398 : CollatzResearch.WordTrace tailWord_7302398 prefixEnd_7302398 3749640104431025567941889 := by
  unfold tailWord_7302398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33292541974833333891600481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177560223865777780755202565 33292541974833333891600481)
  ·
    refine ⟨24969406481125000418700361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33292541974833333891600481 24969406481125000418700361)
    ·
      refine ⟨18727054860843750314025271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24969406481125000418700361 18727054860843750314025271)
      ·
        refine ⟨28090582291265625471037907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18727054860843750314025271 28090582291265625471037907)
        ·
          refine ⟨42135873436898438206556861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28090582291265625471037907 42135873436898438206556861)
          ·
            refine ⟨15800952538836914327458823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42135873436898438206556861 15800952538836914327458823)
            ·
              refine ⟨23701428808255371491188235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15800952538836914327458823 23701428808255371491188235)
              ·
                refine ⟨35552143212383057236782353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23701428808255371491188235 35552143212383057236782353)
                ·
                  refine ⟨26664107409287292927586765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35552143212383057236782353 26664107409287292927586765)
                  ·
                    refine ⟨9999040278482734847845037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26664107409287292927586765 9999040278482734847845037)
                    ·
                      refine ⟨3749640104431025567941889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999040278482734847845037 3749640104431025567941889)
                      ·
                        rfl

theorem cell23_7302398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_7302398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302398 prefixEnd_7302398 := by exact prefixLift 7302398
  have htrace : WordTrace (prefixWord ++ tailWord_7302398) baseStart_7302398 baseEnd_7302398 := by
    simpa [prefixWord, tailWord_7302398, baseEnd_7302398] using wordTrace_append hprefix tailTrace_7302398
  have hstable : (prefixWord ++ tailWord_7302398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302398).length < 2 ^ (prefixWord ++ tailWord_7302398).sum := by decide
  have hdescent : baseEnd_7302398 < baseStart_7302398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302421 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_7302421 : Nat := 118140960795 + 7302421 * 2 ^ 59
def prefixEnd_7302421 : Nat := 4983230072969 + 3 ^ 40 * 7302421 * 2
def baseEnd_7302421 : Nat := 3749651914486078977954283

theorem tailTrace_7302421 : CollatzResearch.WordTrace tailWord_7302421 prefixEnd_7302421 3749651914486078977954283 := by
  unfold tailWord_7302421
  simp only [CollatzResearch.WordTrace]
  refine ⟨266341174677583346060891117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177560783118388897373927411 266341174677583346060891117)
  ·
    refine ⟨99877940504093754772834169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266341174677583346060891117 99877940504093754772834169)
    ·
      refine ⟨74908455378070316079625627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99877940504093754772834169 74908455378070316079625627)
      ·
        refine ⟨112362683067105474119438441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74908455378070316079625627 112362683067105474119438441)
        ·
          refine ⟨84272012300329105589578831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112362683067105474119438441 84272012300329105589578831)
          ·
            refine ⟨126408018450493658384368247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84272012300329105589578831 126408018450493658384368247)
            ·
              refine ⟨189612027675740487576552371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126408018450493658384368247 189612027675740487576552371)
              ·
                refine ⟨284418041513610731364828557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189612027675740487576552371 284418041513610731364828557)
                ·
                  refine ⟨106656765567604024261810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284418041513610731364828557 106656765567604024261810709)
                  ·
                    refine ⟨4999535885981438637272377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106656765567604024261810709 4999535885981438637272377)
                    ·
                      refine ⟨3749651914486078977954283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999535885981438637272377 3749651914486078977954283)
                      ·
                        rfl

theorem cell23_7302421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_7302421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302421 prefixEnd_7302421 := by exact prefixLift 7302421
  have htrace : WordTrace (prefixWord ++ tailWord_7302421) baseStart_7302421 baseEnd_7302421 := by
    simpa [prefixWord, tailWord_7302421, baseEnd_7302421] using wordTrace_append hprefix tailTrace_7302421
  have hstable : (prefixWord ++ tailWord_7302421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302421).length < 2 ^ (prefixWord ++ tailWord_7302421).sum := by decide
  have hdescent : baseEnd_7302421 < baseStart_7302421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302448 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 1, 4]
def baseStart_7302448 : Nat := 118140960795 + 7302448 * 2 ^ 59
def prefixEnd_7302448 : Nat := 4983230072969 + 3 ^ 40 * 7302448 * 2
def baseEnd_7302448 : Nat := 1249888592821250124105553

theorem tailTrace_7302448 : CollatzResearch.WordTrace tailWord_7302448 prefixEnd_7302448 1249888592821250124105553 := by
  unfold tailWord_7302448
  simp only [CollatzResearch.WordTrace]
  refine ⟨133171079724242764836061999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177561439632323686448082665 133171079724242764836061999)
  ·
    refine ⟨199756619586364147254092999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133171079724242764836061999 199756619586364147254092999)
    ·
      refine ⟨299634929379546220881139499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199756619586364147254092999 299634929379546220881139499)
      ·
        refine ⟨449452394069319331321709249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299634929379546220881139499 449452394069319331321709249)
        ·
          refine ⟨337089295551989498491281937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449452394069319331321709249 337089295551989498491281937)
          ·
            refine ⟨252816971663992123868461453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337089295551989498491281937 252816971663992123868461453)
            ·
              refine ⟨94806364373997046450673045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252816971663992123868461453 94806364373997046450673045)
              ·
                refine ⟨4444048330031111552375299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94806364373997046450673045 4444048330031111552375299)
                ·
                  refine ⟨6666072495046667328562949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444048330031111552375299 6666072495046667328562949)
                  ·
                    refine ⟨1249888592821250124105553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6666072495046667328562949 1249888592821250124105553)
                    ·
                      rfl

theorem cell23_7302448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 4].length) (baseStart_7302448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302448 prefixEnd_7302448 := by exact prefixLift 7302448
  have htrace : WordTrace (prefixWord ++ tailWord_7302448) baseStart_7302448 baseEnd_7302448 := by
    simpa [prefixWord, tailWord_7302448, baseEnd_7302448] using wordTrace_append hprefix tailTrace_7302448
  have hstable : (prefixWord ++ tailWord_7302448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302448).length < 2 ^ (prefixWord ++ tailWord_7302448).sum := by decide
  have hdescent : baseEnd_7302448 < baseStart_7302448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302464 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_7302464 : Nat := 118140960795 + 7302464 * 2 ^ 59
def prefixEnd_7302464 : Nat := 4983230072969 + 3 ^ 40 * 7302464 * 2
def baseEnd_7302464 : Nat := 3749673994154222309716585

theorem tailTrace_7302464 : CollatzResearch.WordTrace tailWord_7302464 prefixEnd_7302464 3749673994154222309716585 := by
  unfold tailWord_7302464
  simp only [CollatzResearch.WordTrace]
  refine ⟨133171371508213782202353223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177561828677618376269804297 133171371508213782202353223)
  ·
    refine ⟨199757057262320673303529835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133171371508213782202353223 199757057262320673303529835)
    ·
      refine ⟨299635585893481009955294753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199757057262320673303529835 299635585893481009955294753)
      ·
        refine ⟨224726689420110757466471065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299635585893481009955294753 224726689420110757466471065)
        ·
          refine ⟨168545017065083068099853299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224726689420110757466471065 168545017065083068099853299)
          ·
            refine ⟨252817525597624602149779949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168545017065083068099853299 252817525597624602149779949)
            ·
              refine ⟨94806572099109225806167481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252817525597624602149779949 94806572099109225806167481)
              ·
                refine ⟨71104929074331919354625611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94806572099109225806167481 71104929074331919354625611)
                ·
                  refine ⟨106657393611497879031938417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71104929074331919354625611 106657393611497879031938417)
                  ·
                    refine ⟨79993045208623409273953813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106657393611497879031938417 79993045208623409273953813)
                    ·
                      refine ⟨3749673994154222309716585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79993045208623409273953813 3749673994154222309716585)
                      ·
                        rfl

theorem cell23_7302464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_7302464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302464 prefixEnd_7302464 := by exact prefixLift 7302464
  have htrace : WordTrace (prefixWord ++ tailWord_7302464) baseStart_7302464 baseEnd_7302464 := by
    simpa [prefixWord, tailWord_7302464, baseEnd_7302464] using wordTrace_append hprefix tailTrace_7302464
  have hstable : (prefixWord ++ tailWord_7302464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302464).length < 2 ^ (prefixWord ++ tailWord_7302464).sum := by decide
  have hdescent : baseEnd_7302464 < baseStart_7302464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302474 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_7302474 : Nat := 118140960795 + 7302474 * 2 ^ 59
def prefixEnd_7302474 : Nat := 4983230072969 + 3 ^ 40 * 7302474 * 2
def baseEnd_7302474 : Nat := 1249893042986922423530513

theorem tailTrace_7302474 : CollatzResearch.WordTrace tailWord_7302474 prefixEnd_7302474 1249893042986922423530513 := by
  unfold tailWord_7302474
  simp only [CollatzResearch.WordTrace]
  refine ⟨66585776936597834028142619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177562071830927557408380317 66585776936597834028142619)
  ·
    refine ⟨99878665404896751042213929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66585776936597834028142619 99878665404896751042213929)
    ·
      refine ⟨74908999053672563281660447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99878665404896751042213929 74908999053672563281660447)
      ·
        refine ⟨112363498580508844922490671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74908999053672563281660447 112363498580508844922490671)
        ·
          refine ⟨168545247870763267383736007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112363498580508844922490671 168545247870763267383736007)
          ·
            refine ⟨252817871806144901075604011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168545247870763267383736007 252817871806144901075604011)
            ·
              refine ⟨379226807709217351613406017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252817871806144901075604011 379226807709217351613406017)
              ·
                refine ⟨284420105781913013710054513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379226807709217351613406017 284420105781913013710054513)
                ·
                  refine ⟨213315079336434760282540885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284420105781913013710054513 213315079336434760282540885)
                  ·
                    refine ⟨1249893042986922423530513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 213315079336434760282540885 1249893042986922423530513)
                    ·
                      rfl

theorem cell23_7302474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_7302474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302474 prefixEnd_7302474 := by exact prefixLift 7302474
  have htrace : WordTrace (prefixWord ++ tailWord_7302474) baseStart_7302474 baseEnd_7302474 := by
    simpa [prefixWord, tailWord_7302474, baseEnd_7302474] using wordTrace_append hprefix tailTrace_7302474
  have hstable : (prefixWord ++ tailWord_7302474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302474).length < 2 ^ (prefixWord ++ tailWord_7302474).sum := by decide
  have hdescent : baseEnd_7302474 < baseStart_7302474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302511 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_7302511 : Nat := 118140960795 + 7302511 * 2 ^ 59
def prefixEnd_7302511 : Nat := 4983230072969 + 3 ^ 40 * 7302511 * 2
def baseEnd_7302511 : Nat := 3749698127744983625828869

theorem tailTrace_7302511 : CollatzResearch.WordTrace tailWord_7302511 prefixEnd_7302511 3749698127744983625828869 := by
  unfold tailWord_7302511
  simp only [CollatzResearch.WordTrace]
  refine ⟨266344457247257291431667387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177562971498171527621111591 266344457247257291431667387)
  ·
    refine ⟨399516685870885937147501081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266344457247257291431667387 399516685870885937147501081)
    ·
      refine ⟨299637514403164452860625811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399516685870885937147501081 299637514403164452860625811)
      ·
        refine ⟨449456271604746679290938717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299637514403164452860625811 449456271604746679290938717)
        ·
          refine ⟨168546101851780004734102019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449456271604746679290938717 168546101851780004734102019)
          ·
            refine ⟨252819152777670007101153029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168546101851780004734102019 252819152777670007101153029)
            ·
              refine ⟨47403591145813126331466193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252819152777670007101153029 47403591145813126331466193)
              ·
                refine ⟨35552693359359844748599645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47403591145813126331466193 35552693359359844748599645)
                ·
                  refine ⟨13332260009759941780724867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35552693359359844748599645 13332260009759941780724867)
                  ·
                    refine ⟨19998390014639912671087301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13332260009759941780724867 19998390014639912671087301)
                    ·
                      refine ⟨3749698127744983625828869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19998390014639912671087301 3749698127744983625828869)
                      ·
                        rfl

theorem cell23_7302511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_7302511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302511 prefixEnd_7302511 := by exact prefixLift 7302511
  have htrace : WordTrace (prefixWord ++ tailWord_7302511) baseStart_7302511 baseEnd_7302511 := by
    simpa [prefixWord, tailWord_7302511, baseEnd_7302511] using wordTrace_append hprefix tailTrace_7302511
  have hstable : (prefixWord ++ tailWord_7302511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302511).length < 2 ^ (prefixWord ++ tailWord_7302511).sum := by decide
  have hdescent : baseEnd_7302511 < baseStart_7302511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302542 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_7302542 : Nat := 118140960795 + 7302542 * 2 ^ 59
def prefixEnd_7302542 : Nat := 4983230072969 + 3 ^ 40 * 7302542 * 2
def baseEnd_7302542 : Nat := 1249904681881757668180409

theorem tailTrace_7302542 : CollatzResearch.WordTrace tailWord_7302542 prefixEnd_7302542 1249904681881757668180409 := by
  unfold tailWord_7302542
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293198488768122965755735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177563725273429989150697253 33293198488768122965755735)
  ·
    refine ⟨49939797733152184448633603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33293198488768122965755735 49939797733152184448633603)
    ·
      refine ⟨74909696599728276672950405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49939797733152184448633603 74909696599728276672950405)
      ·
        refine ⟨14045568112449051876178201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74909696599728276672950405 14045568112449051876178201)
        ·
          refine ⟨10534176084336788907133651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14045568112449051876178201 10534176084336788907133651)
          ·
            refine ⟨15801264126505183360700477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534176084336788907133651 15801264126505183360700477)
            ·
              refine ⟨5925474047439443760262679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15801264126505183360700477 5925474047439443760262679)
              ·
                refine ⟨8888211071159165640394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925474047439443760262679 8888211071159165640394019)
                ·
                  refine ⟨13332316606738748460591029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8888211071159165640394019 13332316606738748460591029)
                  ·
                    refine ⟨1249904681881757668180409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13332316606738748460591029 1249904681881757668180409)
                    ·
                      rfl

theorem cell23_7302542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_7302542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302542 prefixEnd_7302542 := by exact prefixLift 7302542
  have htrace : WordTrace (prefixWord ++ tailWord_7302542) baseStart_7302542 baseEnd_7302542 := by
    simpa [prefixWord, tailWord_7302542, baseEnd_7302542] using wordTrace_append hprefix tailTrace_7302542
  have hstable : (prefixWord ++ tailWord_7302542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302542).length < 2 ^ (prefixWord ++ tailWord_7302542).sum := by decide
  have hdescent : baseEnd_7302542 < baseStart_7302542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302596 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7302596 : Nat := 118140960795 + 7302596 * 2 ^ 59
def prefixEnd_7302596 : Nat := 4983230072969 + 3 ^ 40 * 7302596 * 2
def baseEnd_7302596 : Nat := 3749741773600615793265979

theorem tailTrace_7302596 : CollatzResearch.WordTrace tailWord_7302596 prefixEnd_7302596 3749741773600615793265979 := by
  unfold tailWord_7302596
  simp only [CollatzResearch.WordTrace]
  refine ⟨133173778725974675474255821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177565038301299567299007761 133173778725974675474255821)
  ·
    refine ⟨49940167022240503302845933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133173778725974675474255821 49940167022240503302845933)
    ·
      refine ⟨18727562633340188738567225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49940167022240503302845933 18727562633340188738567225)
      ·
        refine ⟨14045671975005141553925419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18727562633340188738567225 14045671975005141553925419)
        ·
          refine ⟨21068507962507712330888129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14045671975005141553925419 21068507962507712330888129)
          ·
            refine ⟨15801380971880784248166097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21068507962507712330888129 15801380971880784248166097)
            ·
              refine ⟨11851035728910588186124573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15801380971880784248166097 11851035728910588186124573)
              ·
                refine ⟨4444138398341470569796715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11851035728910588186124573 4444138398341470569796715)
                ·
                  refine ⟨6666207597512205854695073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444138398341470569796715 6666207597512205854695073)
                  ·
                    refine ⟨4999655698134154391021305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6666207597512205854695073 4999655698134154391021305)
                    ·
                      refine ⟨3749741773600615793265979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999655698134154391021305 3749741773600615793265979)
                      ·
                        rfl

theorem cell23_7302596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7302596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302596 prefixEnd_7302596 := by exact prefixLift 7302596
  have htrace : WordTrace (prefixWord ++ tailWord_7302596) baseStart_7302596 baseEnd_7302596 := by
    simpa [prefixWord, tailWord_7302596, baseEnd_7302596] using wordTrace_append hprefix tailTrace_7302596
  have hstable : (prefixWord ++ tailWord_7302596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302596).length < 2 ^ (prefixWord ++ tailWord_7302596).sum := by decide
  have hdescent : baseEnd_7302596 < baseStart_7302596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302612 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7302612 : Nat := 118140960795 + 7302612 * 2 ^ 59
def prefixEnd_7302612 : Nat := 4983230072969 + 3 ^ 40 * 7302612 * 2
def baseEnd_7302612 : Nat := 3749749989291087730665905

theorem tailTrace_7302612 : CollatzResearch.WordTrace tailWord_7302612 prefixEnd_7302612 3749749989291087730665905 := by
  unfold tailWord_7302612
  simp only [CollatzResearch.WordTrace]
  refine ⟨133174070509945692840547045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177565427346594257120729393 133174070509945692840547045)
  ·
    refine ⟨24970138220614817407602571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133174070509945692840547045 24970138220614817407602571)
    ·
      refine ⟨37455207330922226111403857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24970138220614817407602571 37455207330922226111403857)
      ·
        refine ⟨28091405498191669583552893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37455207330922226111403857 28091405498191669583552893)
        ·
          refine ⟨10534277061821876093832335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28091405498191669583552893 10534277061821876093832335)
          ·
            refine ⟨15801415592732814140748503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534277061821876093832335 15801415592732814140748503)
            ·
              refine ⟨23702123389099221211122755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15801415592732814140748503 23702123389099221211122755)
              ·
                refine ⟨35553185083648831816684133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23702123389099221211122755 35553185083648831816684133)
                ·
                  refine ⟨6666222203184155965628275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35553185083648831816684133 6666222203184155965628275)
                  ·
                    refine ⟨9999333304776233948442413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666222203184155965628275 9999333304776233948442413)
                    ·
                      refine ⟨3749749989291087730665905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999333304776233948442413 3749749989291087730665905)
                      ·
                        rfl

theorem cell23_7302612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7302612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302612 prefixEnd_7302612 := by exact prefixLift 7302612
  have htrace : WordTrace (prefixWord ++ tailWord_7302612) baseStart_7302612 baseEnd_7302612 := by
    simpa [prefixWord, tailWord_7302612, baseEnd_7302612] using wordTrace_append hprefix tailTrace_7302612
  have hstable : (prefixWord ++ tailWord_7302612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302612).length < 2 ^ (prefixWord ++ tailWord_7302612).sum := by decide
  have hdescent : baseEnd_7302612 < baseStart_7302612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302629 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7302629 : Nat := 118140960795 + 7302629 * 2 ^ 59
def prefixEnd_7302629 : Nat := 4983230072969 + 3 ^ 40 * 7302629 * 2
def baseEnd_7302629 : Nat := 3749758718462214164153327

theorem tailTrace_7302629 : CollatzResearch.WordTrace tailWord_7302629 prefixEnd_7302629 3749758718462214164153327 := by
  unfold tailWord_7302629
  simp only [CollatzResearch.WordTrace]
  refine ⟨266348761060829797584462941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177565840707219865056308627 266348761060829797584462941)
  ·
    refine ⟨99880785397811174094173603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266348761060829797584462941 99880785397811174094173603)
    ·
      refine ⟨149821178096716761141260405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99880785397811174094173603 149821178096716761141260405)
      ·
        refine ⟨14045735446567196356993163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149821178096716761141260405 14045735446567196356993163)
        ·
          refine ⟨21068603169850794535489745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14045735446567196356993163 21068603169850794535489745)
          ·
            refine ⟨15801452377388095901617309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21068603169850794535489745 15801452377388095901617309)
            ·
              refine ⟨5925544641520535963106491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15801452377388095901617309 5925544641520535963106491)
              ·
                refine ⟨8888316962280803944659737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925544641520535963106491 8888316962280803944659737)
                ·
                  refine ⟨6666237721710602958494803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8888316962280803944659737 6666237721710602958494803)
                  ·
                    refine ⟨9999356582565904437742205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666237721710602958494803 9999356582565904437742205)
                    ·
                      refine ⟨3749758718462214164153327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999356582565904437742205 3749758718462214164153327)
                      ·
                        rfl

theorem cell23_7302629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7302629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302629 prefixEnd_7302629 := by exact prefixLift 7302629
  have htrace : WordTrace (prefixWord ++ tailWord_7302629) baseStart_7302629 baseEnd_7302629 := by
    simpa [prefixWord, tailWord_7302629, baseEnd_7302629] using wordTrace_append hprefix tailTrace_7302629
  have hstable : (prefixWord ++ tailWord_7302629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302629).length < 2 ^ (prefixWord ++ tailWord_7302629).sum := by decide
  have hdescent : baseEnd_7302629 < baseStart_7302629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302638 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7302638 : Nat := 118140960795 + 7302638 * 2 ^ 59
def prefixEnd_7302638 : Nat := 4983230072969 + 3 ^ 40 * 7302638 * 2
def baseEnd_7302638 : Nat := 3749763339788104628940785

theorem tailTrace_7302638 : CollatzResearch.WordTrace tailWord_7302638 prefixEnd_7302638 3749763339788104628940785 := by
  unfold tailWord_7302638
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293636164724649015192571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177566059545198128081027045 33293636164724649015192571)
  ·
    refine ⟨49940454247086973522788857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33293636164724649015192571 49940454247086973522788857)
    ·
      refine ⟨37455340685315230142091643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49940454247086973522788857 37455340685315230142091643)
      ·
        refine ⟨56183011027972845213137465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37455340685315230142091643 56183011027972845213137465)
        ·
          refine ⟨42137258270979633909853099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56183011027972845213137465 42137258270979633909853099)
          ·
            refine ⟨63205887406469450864779649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42137258270979633909853099 63205887406469450864779649)
            ·
              refine ⟨47404415554852088148584737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63205887406469450864779649 47404415554852088148584737)
              ·
                refine ⟨35553311666139066111438553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47404415554852088148584737 35553311666139066111438553)
                ·
                  refine ⟨26664983749604299583578915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35553311666139066111438553 26664983749604299583578915)
                  ·
                    refine ⟨39997475624406449375368373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26664983749604299583578915 39997475624406449375368373)
                    ·
                      refine ⟨3749763339788104628940785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39997475624406449375368373 3749763339788104628940785)
                      ·
                        rfl

theorem cell23_7302638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7302638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302638 prefixEnd_7302638 := by exact prefixLift 7302638
  have htrace : WordTrace (prefixWord ++ tailWord_7302638) baseStart_7302638 baseEnd_7302638 := by
    simpa [prefixWord, tailWord_7302638, baseEnd_7302638] using wordTrace_append hprefix tailTrace_7302638
  have hstable : (prefixWord ++ tailWord_7302638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302638).length < 2 ^ (prefixWord ++ tailWord_7302638).sum := by decide
  have hdescent : baseEnd_7302638 < baseStart_7302638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302698 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7302698 : Nat := 118140960795 + 7302698 * 2 ^ 59
def prefixEnd_7302698 : Nat := 4983230072969 + 3 ^ 40 * 7302698 * 2
def baseEnd_7302698 : Nat := 3749794148627374394190509

theorem tailTrace_7302698 : CollatzResearch.WordTrace tailWord_7302698 prefixEnd_7302698 3749794148627374394190509 := by
  unfold tailWord_7302698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66587819424394955592181187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177567518465053214912483165 66587819424394955592181187)
  ·
    refine ⟨99881729136592433388271781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66587819424394955592181187 99881729136592433388271781)
    ·
      refine ⟨18727824213111081260300959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99881729136592433388271781 18727824213111081260300959)
      ·
        refine ⟨28091736319666621890451439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18727824213111081260300959 28091736319666621890451439)
        ·
          refine ⟨42137604479499932835677159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28091736319666621890451439 42137604479499932835677159)
          ·
            refine ⟨63206406719249899253515739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42137604479499932835677159 63206406719249899253515739)
            ·
              refine ⟨94809610078874848880273609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63206406719249899253515739 94809610078874848880273609)
              ·
                refine ⟨71107207559156136660205207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94809610078874848880273609 71107207559156136660205207)
                ·
                  refine ⟨106660811338734204990307811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71107207559156136660205207 106660811338734204990307811)
                  ·
                    refine ⟨159991217008101307485461717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106660811338734204990307811 159991217008101307485461717)
                    ·
                      refine ⟨3749794148627374394190509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159991217008101307485461717 3749794148627374394190509)
                      ·
                        rfl

theorem cell23_7302698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7302698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302698 prefixEnd_7302698 := by exact prefixLift 7302698
  have htrace : WordTrace (prefixWord ++ tailWord_7302698) baseStart_7302698 baseEnd_7302698 := by
    simpa [prefixWord, tailWord_7302698, baseEnd_7302698] using wordTrace_append hprefix tailTrace_7302698
  have hstable : (prefixWord ++ tailWord_7302698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302698).length < 2 ^ (prefixWord ++ tailWord_7302698).sum := by decide
  have hdescent : baseEnd_7302698 < baseStart_7302698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302725 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_7302725 : Nat := 118140960795 + 7302725 * 2 ^ 59
def prefixEnd_7302725 : Nat := 4983230072969 + 3 ^ 40 * 7302725 * 2
def baseEnd_7302725 : Nat := 3749808012605045788552885

theorem tailTrace_7302725 : CollatzResearch.WordTrace tailWord_7302725 prefixEnd_7302725 3749808012605045788552885 := by
  unfold tailWord_7302725
  simp only [CollatzResearch.WordTrace]
  refine ⟨266352262468482005979957629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177568174978988003986638419 266352262468482005979957629)
  ·
    refine ⟨99882098425680752242484111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266352262468482005979957629 99882098425680752242484111)
    ·
      refine ⟨149823147638521128363726167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99882098425680752242484111 149823147638521128363726167)
      ·
        refine ⟨224734721457781692545589251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149823147638521128363726167 224734721457781692545589251)
        ·
          refine ⟨337102082186672538818383877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224734721457781692545589251 337102082186672538818383877)
          ·
            refine ⟨63206640410001101028446977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337102082186672538818383877 63206640410001101028446977)
            ·
              refine ⟨47404980307500825771335233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63206640410001101028446977 47404980307500825771335233)
              ·
                refine ⟨35553735230625619328501425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47404980307500825771335233 35553735230625619328501425)
                ·
                  refine ⟨26665301422969214496376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35553735230625619328501425 26665301422969214496376069)
                  ·
                    refine ⟨4999744016806727718070513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26665301422969214496376069 4999744016806727718070513)
                    ·
                      refine ⟨3749808012605045788552885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999744016806727718070513 3749808012605045788552885)
                      ·
                        rfl

theorem cell23_7302725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_7302725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302725 prefixEnd_7302725 := by exact prefixLift 7302725
  have htrace : WordTrace (prefixWord ++ tailWord_7302725) baseStart_7302725 baseEnd_7302725 := by
    simpa [prefixWord, tailWord_7302725, baseEnd_7302725] using wordTrace_append hprefix tailTrace_7302725
  have hstable : (prefixWord ++ tailWord_7302725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302725).length < 2 ^ (prefixWord ++ tailWord_7302725).sum := by decide
  have hdescent : baseEnd_7302725 < baseStart_7302725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302728 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_7302728 : Nat := 118140960795 + 7302728 * 2 ^ 59
def prefixEnd_7302728 : Nat := 4983230072969 + 3 ^ 40 * 7302728 * 2
def baseEnd_7302728 : Nat := 3749809553047009276815371

theorem tailTrace_7302728 : CollatzResearch.WordTrace tailWord_7302728 prefixEnd_7302728 3749809553047009276815371 := by
  unfold tailWord_7302728
  simp only [CollatzResearch.WordTrace]
  refine ⟨133176185943735568746158419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177568247924980758328211225 133176185943735568746158419)
  ·
    refine ⟨199764278915603353119237629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133176185943735568746158419 199764278915603353119237629)
    ·
      refine ⟨74911604593351257419714111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199764278915603353119237629 74911604593351257419714111)
      ·
        refine ⟨112367406890026886129571167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74911604593351257419714111 112367406890026886129571167)
        ·
          refine ⟨168551110335040329194356751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112367406890026886129571167 168551110335040329194356751)
          ·
            refine ⟨252826665502560493791535127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168551110335040329194356751 252826665502560493791535127)
            ·
              refine ⟨379239998253840740687302691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252826665502560493791535127 379239998253840740687302691)
              ·
                refine ⟨568859997380761111030954037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379239998253840740687302691 568859997380761111030954037)
                ·
                  refine ⟨53330624754446354159151941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568859997380761111030954037 53330624754446354159151941)
                  ·
                    refine ⟨9999492141458691404840989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53330624754446354159151941 9999492141458691404840989)
                    ·
                      refine ⟨3749809553047009276815371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999492141458691404840989 3749809553047009276815371)
                      ·
                        rfl

theorem cell23_7302728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_7302728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302728 prefixEnd_7302728 := by exact prefixLift 7302728
  have htrace : WordTrace (prefixWord ++ tailWord_7302728) baseStart_7302728 baseEnd_7302728 := by
    simpa [prefixWord, tailWord_7302728, baseEnd_7302728] using wordTrace_append hprefix tailTrace_7302728
  have hstable : (prefixWord ++ tailWord_7302728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302728).length < 2 ^ (prefixWord ++ tailWord_7302728).sum := by decide
  have hdescent : baseEnd_7302728 < baseStart_7302728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302762 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_7302762 : Nat := 118140960795 + 7302762 * 2 ^ 59
def prefixEnd_7302762 : Nat := 4983230072969 + 3 ^ 40 * 7302762 * 2
def baseEnd_7302762 : Nat := 3749827011389262143790215

theorem tailTrace_7302762 : CollatzResearch.WordTrace tailWord_7302762 prefixEnd_7302762 3749827011389262143790215 := by
  unfold tailWord_7302762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66588402992336990324763635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177569074646231974199369693 66588402992336990324763635)
  ·
    refine ⟨99882604488505485487145453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66588402992336990324763635 99882604488505485487145453)
    ·
      refine ⟨37455976683189557057679545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99882604488505485487145453 37455976683189557057679545)
      ·
        refine ⟨28091982512392167793259659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37455976683189557057679545 28091982512392167793259659)
        ·
          refine ⟨42137973768588251689889489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28091982512392167793259659 42137973768588251689889489)
          ·
            refine ⟨31603480326441188767417117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42137973768588251689889489 31603480326441188767417117)
            ·
              refine ⟨11851305122415445787781419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31603480326441188767417117 11851305122415445787781419)
              ·
                refine ⟨17776957683623168681672129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11851305122415445787781419 17776957683623168681672129)
                ·
                  refine ⟨13332718262717376511254097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17776957683623168681672129 13332718262717376511254097)
                  ·
                    refine ⟨9999538697038032383440573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13332718262717376511254097 9999538697038032383440573)
                    ·
                      refine ⟨3749827011389262143790215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999538697038032383440573 3749827011389262143790215)
                      ·
                        rfl

theorem cell23_7302762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_7302762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302762 prefixEnd_7302762 := by exact prefixLift 7302762
  have htrace : WordTrace (prefixWord ++ tailWord_7302762) baseStart_7302762 baseEnd_7302762 := by
    simpa [prefixWord, tailWord_7302762, baseEnd_7302762] using wordTrace_append hprefix tailTrace_7302762
  have hstable : (prefixWord ++ tailWord_7302762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302762).length < 2 ^ (prefixWord ++ tailWord_7302762).sum := by decide
  have hdescent : baseEnd_7302762 < baseStart_7302762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302775 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_7302775 : Nat := 118140960795 + 7302775 * 2 ^ 59
def prefixEnd_7302775 : Nat := 4983230072969 + 3 ^ 40 * 7302775 * 2
def baseEnd_7302775 : Nat := 3749833686637770592927655

theorem tailTrace_7302775 : CollatzResearch.WordTrace tailWord_7302775 prefixEnd_7302775 3749833686637770592927655 := by
  unfold tailWord_7302775
  simp only [CollatzResearch.WordTrace]
  refine ⟨266354086118300864519277779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177569390745533909679518519 266354086118300864519277779)
  ·
    refine ⟨399531129177451296778916669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266354086118300864519277779 399531129177451296778916669)
    ·
      refine ⟨149824173441544236292093751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399531129177451296778916669 149824173441544236292093751)
      ·
        refine ⟨224736260162316354438140627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149824173441544236292093751 224736260162316354438140627)
        ·
          refine ⟨337104390243474531657210941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224736260162316354438140627 337104390243474531657210941)
          ·
            refine ⟨126414146341302949371454103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337104390243474531657210941 126414146341302949371454103)
            ·
              refine ⟨189621219511954424057181155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126414146341302949371454103 189621219511954424057181155)
              ·
                refine ⟨284431829267931636085771733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189621219511954424057181155 284431829267931636085771733)
                ·
                  refine ⟨6666370998467147720760275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 284431829267931636085771733 6666370998467147720760275)
                  ·
                    refine ⟨9999556497700721581140413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666370998467147720760275 9999556497700721581140413)
                    ·
                      refine ⟨3749833686637770592927655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999556497700721581140413 3749833686637770592927655)
                      ·
                        rfl

theorem cell23_7302775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_7302775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302775 prefixEnd_7302775 := by exact prefixLift 7302775
  have htrace : WordTrace (prefixWord ++ tailWord_7302775) baseStart_7302775 baseEnd_7302775 := by
    simpa [prefixWord, tailWord_7302775, baseEnd_7302775] using wordTrace_append hprefix tailTrace_7302775
  have hstable : (prefixWord ++ tailWord_7302775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302775).length < 2 ^ (prefixWord ++ tailWord_7302775).sum := by decide
  have hdescent : baseEnd_7302775 < baseStart_7302775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302778 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_7302778 : Nat := 118140960795 + 7302778 * 2 ^ 59
def prefixEnd_7302778 : Nat := 4983230072969 + 3 ^ 40 * 7302778 * 2
def baseEnd_7302778 : Nat := 1249945075693244693730047

theorem tailTrace_7302778 : CollatzResearch.WordTrace tailWord_7302778 prefixEnd_7302778 1249945075693244693730047 := by
  unfold tailWord_7302778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66588548884322499007909247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177569463691526664021091325 66588548884322499007909247)
  ·
    refine ⟨99882823326483748511863871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66588548884322499007909247 99882823326483748511863871)
    ·
      refine ⟨149824234989725622767795807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99882823326483748511863871 149824234989725622767795807)
      ·
        refine ⟨224736352484588434151693711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149824234989725622767795807 224736352484588434151693711)
        ·
          refine ⟨337104528726882651227540567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224736352484588434151693711 337104528726882651227540567)
          ·
            refine ⟨505656793090323976841310851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337104528726882651227540567 505656793090323976841310851)
            ·
              refine ⟨758485189635485965261966277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505656793090323976841310851 758485189635485965261966277)
              ·
                refine ⟨142215973056653618486618677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758485189635485965261966277 142215973056653618486618677)
                ·
                  refine ⟨13332747474061276733120501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142215973056653618486618677 13332747474061276733120501)
                  ·
                    refine ⟨1249945075693244693730047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13332747474061276733120501 1249945075693244693730047)
                    ·
                      rfl

theorem cell23_7302778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_7302778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302778 prefixEnd_7302778 := by exact prefixLift 7302778
  have htrace : WordTrace (prefixWord ++ tailWord_7302778) baseStart_7302778 baseEnd_7302778 := by
    simpa [prefixWord, tailWord_7302778, baseEnd_7302778] using wordTrace_append hprefix tailTrace_7302778
  have hstable : (prefixWord ++ tailWord_7302778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302778).length < 2 ^ (prefixWord ++ tailWord_7302778).sum := by decide
  have hdescent : baseEnd_7302778 < baseStart_7302778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302832 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2]
def baseStart_7302832 : Nat := 118140960795 + 7302832 * 2 ^ 59
def prefixEnd_7302832 : Nat := 4983230072969 + 3 ^ 40 * 7302832 * 2
def baseEnd_7302832 : Nat := 3749862955035076869914893

theorem tailTrace_7302832 : CollatzResearch.WordTrace tailWord_7302832 prefixEnd_7302832 3749862955035076869914893 := by
  unfold tailWord_7302832
  simp only [CollatzResearch.WordTrace]
  refine ⟨133178082539547181627051375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177570776719396242169401833 133178082539547181627051375)
  ·
    refine ⟨199767123809320772440577063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133178082539547181627051375 199767123809320772440577063)
    ·
      refine ⟨299650685713981158660865595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199767123809320772440577063 299650685713981158660865595)
      ·
        refine ⟨449476028570971737991298393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299650685713981158660865595 449476028570971737991298393)
        ·
          refine ⟨337107021428228803493473795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449476028570971737991298393 337107021428228803493473795)
          ·
            refine ⟨505660532142343205240210693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337107021428228803493473795 505660532142343205240210693)
            ·
              refine ⟨94811349776689350982539505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 505660532142343205240210693 94811349776689350982539505)
              ·
                refine ⟨71108512332517013236904629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94811349776689350982539505 71108512332517013236904629)
                ·
                  refine ⟨6666423031173469990959809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71108512332517013236904629 6666423031173469990959809)
                  ·
                    refine ⟨4999817273380102493219857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6666423031173469990959809 4999817273380102493219857)
                    ·
                      refine ⟨3749862955035076869914893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999817273380102493219857 3749862955035076869914893)
                      ·
                        rfl

theorem cell23_7302832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2].length) (baseStart_7302832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302832 prefixEnd_7302832 := by exact prefixLift 7302832
  have htrace : WordTrace (prefixWord ++ tailWord_7302832) baseStart_7302832 baseEnd_7302832 := by
    simpa [prefixWord, tailWord_7302832, baseEnd_7302832] using wordTrace_append hprefix tailTrace_7302832
  have hstable : (prefixWord ++ tailWord_7302832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302832).length < 2 ^ (prefixWord ++ tailWord_7302832).sum := by decide
  have hdescent : baseEnd_7302832 < baseStart_7302832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302835 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5]
def baseStart_7302835 : Nat := 118140960795 + 7302835 * 2 ^ 59
def prefixEnd_7302835 : Nat := 4983230072969 + 3 ^ 40 * 7302835 * 2
def baseEnd_7302835 : Nat := 3749864495477040358177379

theorem tailTrace_7302835 : CollatzResearch.WordTrace tailWord_7302835 prefixEnd_7302835 3749864495477040358177379 := by
  unfold tailWord_7302835
  simp only [CollatzResearch.WordTrace]
  refine ⟨266356274498083494766461959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177570849665388996510974639 266356274498083494766461959)
  ·
    refine ⟨399534411747125242149692939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266356274498083494766461959 399534411747125242149692939)
    ·
      refine ⟨599301617620687863224539409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399534411747125242149692939 599301617620687863224539409)
      ·
        refine ⟨449476213215515897418404557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599301617620687863224539409 449476213215515897418404557)
        ·
          refine ⟨168553579955818461531901709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449476213215515897418404557 168553579955818461531901709)
          ·
            refine ⟨63207592483431923074463141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168553579955818461531901709 63207592483431923074463141)
            ·
              refine ⟨11851423590643485576461839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63207592483431923074463141 11851423590643485576461839)
              ·
                refine ⟨17777135385965228364692759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11851423590643485576461839 17777135385965228364692759)
                ·
                  refine ⟨26665703078947842547039139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17777135385965228364692759 26665703078947842547039139)
                  ·
                    refine ⟨39998554618421763820558709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26665703078947842547039139 39998554618421763820558709)
                    ·
                      refine ⟨3749864495477040358177379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39998554618421763820558709 3749864495477040358177379)
                      ·
                        rfl

theorem cell23_7302835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_7302835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302835 prefixEnd_7302835 := by exact prefixLift 7302835
  have htrace : WordTrace (prefixWord ++ tailWord_7302835) baseStart_7302835 baseEnd_7302835 := by
    simpa [prefixWord, tailWord_7302835, baseEnd_7302835] using wordTrace_append hprefix tailTrace_7302835
  have hstable : (prefixWord ++ tailWord_7302835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302835).length < 2 ^ (prefixWord ++ tailWord_7302835).sum := by decide
  have hdescent : baseEnd_7302835 < baseStart_7302835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302850 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7302850 : Nat := 118140960795 + 7302850 * 2 ^ 59
def prefixEnd_7302850 : Nat := 4983230072969 + 3 ^ 40 * 7302850 * 2
def baseEnd_7302850 : Nat := 416652466409650866609979

theorem tailTrace_7302850 : CollatzResearch.WordTrace tailWord_7302850 prefixEnd_7302850 416652466409650866609979 := by
  unfold tailWord_7302850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66589205398257288082064501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177571214395352768218838669 66589205398257288082064501)
  ·
    refine ⟨6242738006086620757693547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66589205398257288082064501 6242738006086620757693547)
    ·
      refine ⟨9364107009129931136540321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242738006086620757693547 9364107009129931136540321)
      ·
        refine ⟨7023080256847448352405241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364107009129931136540321 7023080256847448352405241)
        ·
          refine ⟨5267310192635586264303931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7023080256847448352405241 5267310192635586264303931)
          ·
            refine ⟨7900965288953379396455897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267310192635586264303931 7900965288953379396455897)
            ·
              refine ⟨5925723966715034547341923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900965288953379396455897 5925723966715034547341923)
              ·
                refine ⟨8888585950072551821012885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925723966715034547341923 8888585950072551821012885)
                ·
                  refine ⟨416652466409650866609979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8888585950072551821012885 416652466409650866609979)
                  ·
                    rfl

theorem cell23_7302850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7302850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302850 prefixEnd_7302850 := by exact prefixLift 7302850
  have htrace : WordTrace (prefixWord ++ tailWord_7302850) baseStart_7302850 baseEnd_7302850 := by
    simpa [prefixWord, tailWord_7302850, baseEnd_7302850] using wordTrace_append hprefix tailTrace_7302850
  have hstable : (prefixWord ++ tailWord_7302850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302850).length < 2 ^ (prefixWord ++ tailWord_7302850).sum := by decide
  have hdescent : baseEnd_7302850 < baseStart_7302850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302852 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7302852 : Nat := 118140960795 + 7302852 * 2 ^ 59
def prefixEnd_7302852 : Nat := 4983230072969 + 3 ^ 40 * 7302852 * 2
def baseEnd_7302852 : Nat := 3749873224648166791664801

theorem tailTrace_7302852 : CollatzResearch.WordTrace tailWord_7302852 prefixEnd_7302852 3749873224648166791664801 := by
  unfold tailWord_7302852
  simp only [CollatzResearch.WordTrace]
  refine ⟨133178447269510953334915405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177571263026014604446553873 133178447269510953334915405)
  ·
    refine ⟨49941917726066607500593277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133178447269510953334915405 49941917726066607500593277)
    ·
      refine ⟨18728219147274977812722479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49941917726066607500593277 18728219147274977812722479)
      ·
        refine ⟨28092328720912466719083719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18728219147274977812722479 28092328720912466719083719)
        ·
          refine ⟨42138493081368700078625579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28092328720912466719083719 42138493081368700078625579)
          ·
            refine ⟨63207739622053050117938369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42138493081368700078625579 63207739622053050117938369)
            ·
              refine ⟨47405804716539787588453777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63207739622053050117938369 47405804716539787588453777)
              ·
                refine ⟨35554353537404840691340333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47405804716539787588453777 35554353537404840691340333)
                ·
                  refine ⟨13332882576526815259252625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35554353537404840691340333 13332882576526815259252625)
                  ·
                    refine ⟨9999661932395111444439469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13332882576526815259252625 9999661932395111444439469)
                    ·
                      refine ⟨3749873224648166791664801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999661932395111444439469 3749873224648166791664801)
                      ·
                        rfl

theorem cell23_7302852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7302852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302852 prefixEnd_7302852 := by exact prefixLift 7302852
  have htrace : WordTrace (prefixWord ++ tailWord_7302852) baseStart_7302852 baseEnd_7302852 := by
    simpa [prefixWord, tailWord_7302852, baseEnd_7302852] using wordTrace_append hprefix tailTrace_7302852
  have hstable : (prefixWord ++ tailWord_7302852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302852).length < 2 ^ (prefixWord ++ tailWord_7302852).sum := by decide
  have hdescent : baseEnd_7302852 < baseStart_7302852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302952 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7302952 : Nat := 118140960795 + 7302952 * 2 ^ 59
def prefixEnd_7302952 : Nat := 4983230072969 + 3 ^ 40 * 7302952 * 2
def baseEnd_7302952 : Nat := 3749924572713616400414341

theorem tailTrace_7302952 : CollatzResearch.WordTrace tailWord_7302952 prefixEnd_7302952 3749924572713616400414341 := by
  unfold tailWord_7302952
  simp only [CollatzResearch.WordTrace]
  refine ⟨133180270919329811874235555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177573694559106415832314073 133180270919329811874235555)
  ·
    refine ⟨199770406378994717811353333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133180270919329811874235555 199770406378994717811353333)
    ·
      refine ⟨18728475598030754794814375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199770406378994717811353333 18728475598030754794814375)
      ·
        refine ⟨28092713397046132192221563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18728475598030754794814375 28092713397046132192221563)
        ·
          refine ⟨42139070095569198288332345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28092713397046132192221563 42139070095569198288332345)
          ·
            refine ⟨31604302571676898716249259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42139070095569198288332345 31604302571676898716249259)
            ·
              refine ⟨47406453857515348074373889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31604302571676898716249259 47406453857515348074373889)
              ·
                refine ⟨35554840393136511055780417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47406453857515348074373889 35554840393136511055780417)
                ·
                  refine ⟨26666130294852383291835313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35554840393136511055780417 26666130294852383291835313)
                  ·
                    refine ⟨19999597721139287468876485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26666130294852383291835313 19999597721139287468876485)
                    ·
                      refine ⟨3749924572713616400414341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19999597721139287468876485 3749924572713616400414341)
                      ·
                        rfl

theorem cell23_7302952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7302952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302952 prefixEnd_7302952 := by exact prefixLift 7302952
  have htrace : WordTrace (prefixWord ++ tailWord_7302952) baseStart_7302952 baseEnd_7302952 := by
    simpa [prefixWord, tailWord_7302952, baseEnd_7302952] using wordTrace_append hprefix tailTrace_7302952
  have hstable : (prefixWord ++ tailWord_7302952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302952).length < 2 ^ (prefixWord ++ tailWord_7302952).sum := by decide
  have hdescent : baseEnd_7302952 < baseStart_7302952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302956 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_7302956 : Nat := 118140960795 + 7302956 * 2 ^ 59
def prefixEnd_7302956 : Nat := 4983230072969 + 3 ^ 40 * 7302956 * 2
def baseEnd_7302956 : Nat := 3749926626636234384764323

theorem tailTrace_7302956 : CollatzResearch.WordTrace tailWord_7302956 prefixEnd_7302956 3749926626636234384764323 := by
  unfold tailWord_7302956
  simp only [CollatzResearch.WordTrace]
  refine ⟨133180343865322566215808361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177573791820430088287744481 133180343865322566215808361)
  ·
    refine ⟨99885257898991924661856271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133180343865322566215808361 99885257898991924661856271)
    ·
      refine ⟨149827886848487886992784407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99885257898991924661856271 149827886848487886992784407)
      ·
        refine ⟨224741830272731830489176611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149827886848487886992784407 224741830272731830489176611)
        ·
          refine ⟨337112745409097745733764917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224741830272731830489176611 337112745409097745733764917)
          ·
            refine ⟨31604319882102913662540461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337112745409097745733764917 31604319882102913662540461)
            ·
              refine ⟨11851619955788592623452673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31604319882102913662540461 11851619955788592623452673)
              ·
                refine ⟨8888714966841444467589505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11851619955788592623452673 8888714966841444467589505)
                ·
                  refine ⟨6666536225131083350692129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8888714966841444467589505 6666536225131083350692129)
                  ·
                    refine ⟨4999902168848312513019097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6666536225131083350692129 4999902168848312513019097)
                    ·
                      refine ⟨3749926626636234384764323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999902168848312513019097 3749926626636234384764323)
                      ·
                        rfl

theorem cell23_7302956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_7302956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302956 prefixEnd_7302956 := by exact prefixLift 7302956
  have htrace : WordTrace (prefixWord ++ tailWord_7302956) baseStart_7302956 baseEnd_7302956 := by
    simpa [prefixWord, tailWord_7302956, baseEnd_7302956] using wordTrace_append hprefix tailTrace_7302956
  have hstable : (prefixWord ++ tailWord_7302956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302956).length < 2 ^ (prefixWord ++ tailWord_7302956).sum := by decide
  have hdescent : baseEnd_7302956 < baseStart_7302956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302962 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_7302962 : Nat := 118140960795 + 7302962 * 2 ^ 59
def prefixEnd_7302962 : Nat := 4983230072969 + 3 ^ 40 * 7302962 * 2
def baseEnd_7302962 : Nat := 416658856391129040143255

theorem tailTrace_7302962 : CollatzResearch.WordTrace tailWord_7302962 prefixEnd_7302962 416658856391129040143255 := by
  unfold tailWord_7302962
  simp only [CollatzResearch.WordTrace]
  refine ⟨66590226642155848864083785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177573937712415596970890093 66590226642155848864083785)
  ·
    refine ⟨49942669981616886648062839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66590226642155848864083785 49942669981616886648062839)
    ·
      refine ⟨74914004972425329972094259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49942669981616886648062839 74914004972425329972094259)
      ·
        refine ⟨112371007458637994958141389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74914004972425329972094259 112371007458637994958141389)
        ·
          refine ⟨42139127796989248109303021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112371007458637994958141389 42139127796989248109303021)
          ·
            refine ⟨15802172923870968040988633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42139127796989248109303021 15802172923870968040988633)
            ·
              refine ⟨11851629692903226030741475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15802172923870968040988633 11851629692903226030741475)
              ·
                refine ⟨17777444539354839046112213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11851629692903226030741475 17777444539354839046112213)
                ·
                  refine ⟨416658856391129040143255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17777444539354839046112213 416658856391129040143255)
                  ·
                    rfl

theorem cell23_7302962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_7302962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302962 prefixEnd_7302962 := by exact prefixLift 7302962
  have htrace : WordTrace (prefixWord ++ tailWord_7302962) baseStart_7302962 baseEnd_7302962 := by
    simpa [prefixWord, tailWord_7302962, baseEnd_7302962] using wordTrace_append hprefix tailTrace_7302962
  have hstable : (prefixWord ++ tailWord_7302962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302962).length < 2 ^ (prefixWord ++ tailWord_7302962).sum := by decide
  have hdescent : baseEnd_7302962 < baseStart_7302962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302972 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_7302972 : Nat := 118140960795 + 7302972 * 2 ^ 59
def prefixEnd_7302972 : Nat := 4983230072969 + 3 ^ 40 * 7302972 * 2
def baseEnd_7302972 : Nat := 3749934842326706322164249

theorem tailTrace_7302972 : CollatzResearch.WordTrace tailWord_7302972 prefixEnd_7302972 3749934842326706322164249 := by
  unfold tailWord_7302972
  simp only [CollatzResearch.WordTrace]
  refine ⟨133180635649293583582099585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177574180865724778109466113 133180635649293583582099585)
  ·
    refine ⟨99885476736970187686574689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133180635649293583582099585 99885476736970187686574689)
    ·
      refine ⟨74914107552727640764931017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99885476736970187686574689 74914107552727640764931017)
      ·
        refine ⟨56185580664545730573698263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74914107552727640764931017 56185580664545730573698263)
        ·
          refine ⟨84278370996818595860547395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56185580664545730573698263 84278370996818595860547395)
          ·
            refine ⟨126417556495227893790821093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84278370996818595860547395 126417556495227893790821093)
            ·
              refine ⟨23703291842855230085778955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126417556495227893790821093 23703291842855230085778955)
              ·
                refine ⟨35554937764282845128668433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23703291842855230085778955 35554937764282845128668433)
                ·
                  refine ⟨26666203323212133846501325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35554937764282845128668433 26666203323212133846501325)
                  ·
                    refine ⟨9999826246204550192437997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26666203323212133846501325 9999826246204550192437997)
                    ·
                      refine ⟨3749934842326706322164249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999826246204550192437997 3749934842326706322164249)
                      ·
                        rfl

theorem cell23_7302972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_7302972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302972 prefixEnd_7302972 := by exact prefixLift 7302972
  have htrace : WordTrace (prefixWord ++ tailWord_7302972) baseStart_7302972 baseEnd_7302972 := by
    simpa [prefixWord, tailWord_7302972, baseEnd_7302972] using wordTrace_append hprefix tailTrace_7302972
  have hstable : (prefixWord ++ tailWord_7302972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302972).length < 2 ^ (prefixWord ++ tailWord_7302972).sum := by decide
  have hdescent : baseEnd_7302972 < baseStart_7302972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7302996 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 5]
def baseStart_7302996 : Nat := 118140960795 + 7302996 * 2 ^ 59
def prefixEnd_7302996 : Nat := 4983230072969 + 3 ^ 40 * 7302996 * 2
def baseEnd_7302996 : Nat := 416660796206934914251571

theorem tailTrace_7302996 : CollatzResearch.WordTrace tailWord_7302996 prefixEnd_7302996 416660796206934914251571 := by
  unfold tailWord_7302996
  simp only [CollatzResearch.WordTrace]
  refine ⟨133181073325250109631536421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177574764433666812842048561 133181073325250109631536421)
  ·
    refine ⟨24971451248484395555913079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133181073325250109631536421 24971451248484395555913079)
    ·
      refine ⟨37457176872726593333869619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24971451248484395555913079 37457176872726593333869619)
      ·
        refine ⟨56185765309089890000804429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37457176872726593333869619 56185765309089890000804429)
        ·
          refine ⟨21069661990908708750301661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56185765309089890000804429 21069661990908708750301661)
          ·
            refine ⟨7901123246590765781363123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21069661990908708750301661 7901123246590765781363123)
            ·
              refine ⟨11851684869886148672044685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901123246590765781363123 11851684869886148672044685)
              ·
                refine ⟨4444381826207305752016757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11851684869886148672044685 4444381826207305752016757)
                ·
                  refine ⟨416660796206934914251571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444381826207305752016757 416660796206934914251571)
                  ·
                    rfl

theorem cell23_7302996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_7302996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7302996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7302996 prefixEnd_7302996 := by exact prefixLift 7302996
  have htrace : WordTrace (prefixWord ++ tailWord_7302996) baseStart_7302996 baseEnd_7302996 := by
    simpa [prefixWord, tailWord_7302996, baseEnd_7302996] using wordTrace_append hprefix tailTrace_7302996
  have hstable : (prefixWord ++ tailWord_7302996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7302996).length < 2 ^ (prefixWord ++ tailWord_7302996).sum := by decide
  have hdescent : baseEnd_7302996 < baseStart_7302996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7302996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303029 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7303029 : Nat := 118140960795 + 7303029 * 2 ^ 59
def prefixEnd_7303029 : Nat := 4983230072969 + 3 ^ 40 * 7303029 * 2
def baseEnd_7303029 : Nat := 3749964110724012599151487

theorem tailTrace_7303029 : CollatzResearch.WordTrace tailWord_7303029 prefixEnd_7303029 3749964110724012599151487 := by
  unfold tailWord_7303029
  simp only [CollatzResearch.WordTrace]
  refine ⟨266363350259380665899024141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177575566839587110599349427 266363350259380665899024141)
  ·
    refine ⟨99886256347267749712134053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266363350259380665899024141 99886256347267749712134053)
    ·
      refine ⟨18728673065112703071025135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99886256347267749712134053 18728673065112703071025135)
      ·
        refine ⟨28093009597669054606537703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18728673065112703071025135 28093009597669054606537703)
        ·
          refine ⟨42139514396503581909806555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093009597669054606537703 42139514396503581909806555)
          ·
            refine ⟨63209271594755372864709833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42139514396503581909806555 63209271594755372864709833)
            ·
              refine ⟨47406953696066529648532375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63209271594755372864709833 47406953696066529648532375)
              ·
                refine ⟨71110430544099794472798563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47406953696066529648532375 71110430544099794472798563)
                ·
                  refine ⟨106665645816149691709197845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71110430544099794472798563 106665645816149691709197845)
                  ·
                    refine ⟨4999952147632016798868649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106665645816149691709197845 4999952147632016798868649)
                    ·
                      refine ⟨3749964110724012599151487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4999952147632016798868649 3749964110724012599151487)
                      ·
                        rfl

theorem cell23_7303029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7303029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303029 prefixEnd_7303029 := by exact prefixLift 7303029
  have htrace : WordTrace (prefixWord ++ tailWord_7303029) baseStart_7303029 baseEnd_7303029 := by
    simpa [prefixWord, tailWord_7303029, baseEnd_7303029] using wordTrace_append hprefix tailTrace_7303029
  have hstable : (prefixWord ++ tailWord_7303029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303029).length < 2 ^ (prefixWord ++ tailWord_7303029).sum := by decide
  have hdescent : baseEnd_7303029 < baseStart_7303029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303049 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_7303049 : Nat := 118140960795 + 7303049 * 2 ^ 59
def prefixEnd_7303049 : Nat := 4983230072969 + 3 ^ 40 * 7303049 * 2
def baseEnd_7303049 : Nat := 3749974380337102520901395

theorem tailTrace_7303049 : CollatzResearch.WordTrace tailWord_7303049 prefixEnd_7303049 3749974380337102520901395 := by
  unfold tailWord_7303049
  simp only [CollatzResearch.WordTrace]
  refine ⟨266364079719308209314752201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177576053146205472876501467 266364079719308209314752201)
  ·
    refine ⟨199773059789481156986064151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266364079719308209314752201 199773059789481156986064151)
    ·
      refine ⟨299659589684221735479096227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199773059789481156986064151 299659589684221735479096227)
      ·
        refine ⟨449489384526332603218644341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299659589684221735479096227 449489384526332603218644341)
        ·
          refine ⟨42139629799343681551747907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 449489384526332603218644341 42139629799343681551747907)
          ·
            refine ⟨63209444699015522327621861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42139629799343681551747907 63209444699015522327621861)
            ·
              refine ⟨11851770881065410436429099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63209444699015522327621861 11851770881065410436429099)
              ·
                refine ⟨17777656321598115654643649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11851770881065410436429099 17777656321598115654643649)
                ·
                  refine ⟨13333242241198586740982737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17777656321598115654643649 13333242241198586740982737)
                  ·
                    refine ⟨9999931680898940055737053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13333242241198586740982737 9999931680898940055737053)
                    ·
                      refine ⟨3749974380337102520901395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9999931680898940055737053 3749974380337102520901395)
                      ·
                        rfl

theorem cell23_7303049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_7303049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303049 prefixEnd_7303049 := by exact prefixLift 7303049
  have htrace : WordTrace (prefixWord ++ tailWord_7303049) baseStart_7303049 baseEnd_7303049 := by
    simpa [prefixWord, tailWord_7303049, baseEnd_7303049] using wordTrace_append hprefix tailTrace_7303049
  have hstable : (prefixWord ++ tailWord_7303049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303049).length < 2 ^ (prefixWord ++ tailWord_7303049).sum := by decide
  have hdescent : baseEnd_7303049 < baseStart_7303049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303069 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 6]
def baseStart_7303069 : Nat := 118140960795 + 7303069 * 2 ^ 59
def prefixEnd_7303069 : Nat := 4983230072969 + 3 ^ 40 * 7303069 * 2
def baseEnd_7303069 : Nat := 416664961105576938072367

theorem tailTrace_7303069 : CollatzResearch.WordTrace tailWord_7303069 prefixEnd_7303069 416664961105576938072367 := by
  unfold tailWord_7303069
  simp only [CollatzResearch.WordTrace]
  refine ⟨266364809179235752730480261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177576539452823835153653507 266364809179235752730480261)
  ·
    refine ⟨49943401721106703636965049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266364809179235752730480261 49943401721106703636965049)
    ·
      refine ⟨37457551290830027727723787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49943401721106703636965049 37457551290830027727723787)
      ·
        refine ⟨56186326936245041591585681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37457551290830027727723787 56186326936245041591585681)
        ·
          refine ⟨42139745202183781193689261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56186326936245041591585681 42139745202183781193689261)
          ·
            refine ⟨15802404450818917947633473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42139745202183781193689261 15802404450818917947633473)
            ·
              refine ⟨11851803338114188460725105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15802404450818917947633473 11851803338114188460725105)
              ·
                refine ⟨8888852503585641345543829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11851803338114188460725105 8888852503585641345543829)
                ·
                  refine ⟨416664961105576938072367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8888852503585641345543829 416664961105576938072367)
                  ·
                    rfl

theorem cell23_7303069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_7303069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303069 prefixEnd_7303069 := by exact prefixLift 7303069
  have htrace : WordTrace (prefixWord ++ tailWord_7303069) baseStart_7303069 baseEnd_7303069 := by
    simpa [prefixWord, tailWord_7303069, baseEnd_7303069] using wordTrace_append hprefix tailTrace_7303069
  have hstable : (prefixWord ++ tailWord_7303069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303069).length < 2 ^ (prefixWord ++ tailWord_7303069).sum := by decide
  have hdescent : baseEnd_7303069 < baseStart_7303069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303073 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 1, 4]
def baseStart_7303073 : Nat := 118140960795 + 7303073 * 2 ^ 59
def prefixEnd_7303073 : Nat := 4983230072969 + 3 ^ 40 * 7303073 * 2
def baseEnd_7303073 : Nat := 1249995567957603475667095

theorem tailTrace_7303073 : CollatzResearch.WordTrace tailWord_7303073 prefixEnd_7303073 1249995567957603475667095 := by
  unfold tailWord_7303073
  simp only [CollatzResearch.WordTrace]
  refine ⟨266364955071221261413625873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177576636714147507609083915 266364955071221261413625873)
  ·
    refine ⟨199773716303415946060219405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266364955071221261413625873 199773716303415946060219405)
    ·
      refine ⟨74915143613780979772582277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199773716303415946060219405 74915143613780979772582277)
      ·
        refine ⟨14046589427583933707359177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74915143613780979772582277 14046589427583933707359177)
        ·
          refine ⟨10534942070687950280519383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14046589427583933707359177 10534942070687950280519383)
          ·
            refine ⟨15802413106031925420779075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534942070687950280519383 15802413106031925420779075)
            ·
              refine ⟨23703619659047888131168613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15802413106031925420779075 23703619659047888131168613)
              ·
                refine ⟨4444428686071479024594115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23703619659047888131168613 4444428686071479024594115)
                ·
                  refine ⟨6666643029107218536891173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444428686071479024594115 6666643029107218536891173)
                  ·
                    refine ⟨1249995567957603475667095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6666643029107218536891173 1249995567957603475667095)
                    ·
                      rfl

theorem cell23_7303073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_7303073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303073 prefixEnd_7303073 := by exact prefixLift 7303073
  have htrace : WordTrace (prefixWord ++ tailWord_7303073) baseStart_7303073 baseEnd_7303073 := by
    simpa [prefixWord, tailWord_7303073, baseEnd_7303073] using wordTrace_append hprefix tailTrace_7303073
  have hstable : (prefixWord ++ tailWord_7303073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303073).length < 2 ^ (prefixWord ++ tailWord_7303073).sum := by decide
  have hdescent : baseEnd_7303073 < baseStart_7303073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303100 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7303100 : Nat := 118140960795 + 7303100 * 2 ^ 59
def prefixEnd_7303100 : Nat := 4983230072969 + 3 ^ 40 * 7303100 * 2
def baseEnd_7303100 : Nat := 3750000567850481821363661

theorem tailTrace_7303100 : CollatzResearch.WordTrace tailWord_7303100 prefixEnd_7303100 3750000567850481821363661 := by
  unfold tailWord_7303100
  simp only [CollatzResearch.WordTrace]
  refine ⟨133182969921061722512429377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177577293228082296683239169 133182969921061722512429377)
  ·
    refine ⟨99887227440796291884322033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133182969921061722512429377 99887227440796291884322033)
    ·
      refine ⟨74915420580597218913241525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99887227440796291884322033 74915420580597218913241525)
      ·
        refine ⟨7023320679430989273116393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74915420580597218913241525 7023320679430989273116393)
        ·
          refine ⟨5267490509573241954837295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7023320679430989273116393 5267490509573241954837295)
          ·
            refine ⟨7901235764359862932255943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267490509573241954837295 7901235764359862932255943)
            ·
              refine ⟨11851853646539794398383915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901235764359862932255943 11851853646539794398383915)
              ·
                refine ⟨17777780469809691597575873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11851853646539794398383915 17777780469809691597575873)
                ·
                  refine ⟨13333335352357268698181905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17777780469809691597575873 13333335352357268698181905)
                  ·
                    refine ⟨10000001514267951523636429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13333335352357268698181905 10000001514267951523636429)
                    ·
                      refine ⟨3750000567850481821363661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000001514267951523636429 3750000567850481821363661)
                      ·
                        rfl

theorem cell23_7303100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7303100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303100 prefixEnd_7303100 := by exact prefixLift 7303100
  have htrace : WordTrace (prefixWord ++ tailWord_7303100) baseStart_7303100 baseEnd_7303100 := by
    simpa [prefixWord, tailWord_7303100, baseEnd_7303100] using wordTrace_append hprefix tailTrace_7303100
  have hstable : (prefixWord ++ tailWord_7303100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303100).length < 2 ^ (prefixWord ++ tailWord_7303100).sum := by decide
  have hdescent : baseEnd_7303100 < baseStart_7303100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303116 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_7303116 : Nat := 118140960795 + 7303116 * 2 ^ 59
def prefixEnd_7303116 : Nat := 4983230072969 + 3 ^ 40 * 7303116 * 2
def baseEnd_7303116 : Nat := 1250002927846984586254529

theorem tailTrace_7303116 : CollatzResearch.WordTrace tailWord_7303116 prefixEnd_7303116 1250002927846984586254529 := by
  unfold tailWord_7303116
  simp only [CollatzResearch.WordTrace]
  refine ⟨133183261705032739878720601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177577682273376986504960801 133183261705032739878720601)
  ·
    refine ⟨99887446278774554909040451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133183261705032739878720601 99887446278774554909040451)
    ·
      refine ⟨149831169418161832363560677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99887446278774554909040451 149831169418161832363560677)
      ·
        refine ⟨28093344265905343568167627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149831169418161832363560677 28093344265905343568167627)
        ·
          refine ⟨42140016398858015352251441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093344265905343568167627 42140016398858015352251441)
          ·
            refine ⟨31605012299143511514188581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42140016398858015352251441 31605012299143511514188581)
            ·
              refine ⟨5925939806089408408910359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31605012299143511514188581 5925939806089408408910359)
              ·
                refine ⟨8888909709134112613365539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925939806089408408910359 8888909709134112613365539)
                ·
                  refine ⟨13333364563701168920048309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8888909709134112613365539 13333364563701168920048309)
                  ·
                    refine ⟨1250002927846984586254529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13333364563701168920048309 1250002927846984586254529)
                    ·
                      rfl

theorem cell23_7303116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_7303116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303116 prefixEnd_7303116 := by exact prefixLift 7303116
  have htrace : WordTrace (prefixWord ++ tailWord_7303116) baseStart_7303116 baseEnd_7303116 := by
    simpa [prefixWord, tailWord_7303116, baseEnd_7303116] using wordTrace_append hprefix tailTrace_7303116
  have hstable : (prefixWord ++ tailWord_7303116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303116).length < 2 ^ (prefixWord ++ tailWord_7303116).sum := by decide
  have hdescent : baseEnd_7303116 < baseStart_7303116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303119 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_7303119 : Nat := 118140960795 + 7303119 * 2 ^ 59
def prefixEnd_7303119 : Nat := 4983230072969 + 3 ^ 40 * 7303119 * 2
def baseEnd_7303119 : Nat := 3750010323982917247026073

theorem tailTrace_7303119 : CollatzResearch.WordTrace tailWord_7303119 prefixEnd_7303119 3750010323982917247026073 := by
  unfold tailWord_7303119
  simp only [CollatzResearch.WordTrace]
  refine ⟨266366632829054611269800411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177577755219369740846533607 266366632829054611269800411)
  ·
    refine ⟨399549949243581916904700617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266366632829054611269800411 399549949243581916904700617)
    ·
      refine ⟨299662461932686437678525463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399549949243581916904700617 299662461932686437678525463)
      ·
        refine ⟨449493692899029656517788195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299662461932686437678525463 449493692899029656517788195)
        ·
          refine ⟨674240539348544484776682293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449493692899029656517788195 674240539348544484776682293)
          ·
            refine ⟨63210050563926045447813965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 674240539348544484776682293 63210050563926045447813965)
            ·
              refine ⟨23703768961472267042930237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63210050563926045447813965 23703768961472267042930237)
              ·
                refine ⟨8888913360552100141098839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23703768961472267042930237 8888913360552100141098839)
                ·
                  refine ⟨13333370040828150211648259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8888913360552100141098839 13333370040828150211648259)
                  ·
                    refine ⟨20000055061242225317472389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13333370040828150211648259 20000055061242225317472389)
                    ·
                      refine ⟨3750010323982917247026073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20000055061242225317472389 3750010323982917247026073)
                      ·
                        rfl

theorem cell23_7303119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_7303119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303119 prefixEnd_7303119 := by exact prefixLift 7303119
  have htrace : WordTrace (prefixWord ++ tailWord_7303119) baseStart_7303119 baseEnd_7303119 := by
    simpa [prefixWord, tailWord_7303119, baseEnd_7303119] using wordTrace_append hprefix tailTrace_7303119
  have hstable : (prefixWord ++ tailWord_7303119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303119).length < 2 ^ (prefixWord ++ tailWord_7303119).sum := by decide
  have hdescent : baseEnd_7303119 < baseStart_7303119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303139 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7303139 : Nat := 118140960795 + 7303139 * 2 ^ 59
def prefixEnd_7303139 : Nat := 4983230072969 + 3 ^ 40 * 7303139 * 2
def baseEnd_7303139 : Nat := 3750020593596007168775981

theorem tailTrace_7303139 : CollatzResearch.WordTrace tailWord_7303139 prefixEnd_7303139 3750020593596007168775981 := by
  unfold tailWord_7303139
  simp only [CollatzResearch.WordTrace]
  refine ⟨266367362288982154685528471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177578241525988103123685647 266367362288982154685528471)
  ·
    refine ⟨399551043433473232028292707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266367362288982154685528471 399551043433473232028292707)
    ·
      refine ⟨599326565150209848042439061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399551043433473232028292707 599326565150209848042439061)
      ·
        refine ⟨28093432741416086626989331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 599326565150209848042439061 28093432741416086626989331)
        ·
          refine ⟨42140149112124129940483997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093432741416086626989331 42140149112124129940483997)
          ·
            refine ⟨15802555917046548727681499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42140149112124129940483997 15802555917046548727681499)
            ·
              refine ⟨23703833875569823091522249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15802555917046548727681499 23703833875569823091522249)
              ·
                refine ⟨17777875406677367318641687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23703833875569823091522249 17777875406677367318641687)
                ·
                  refine ⟨26666813110016050977962531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17777875406677367318641687 26666813110016050977962531)
                  ·
                    refine ⟨40000219665024076466943797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26666813110016050977962531 40000219665024076466943797)
                    ·
                      refine ⟨3750020593596007168775981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40000219665024076466943797 3750020593596007168775981)
                      ·
                        rfl

theorem cell23_7303139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7303139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303139 prefixEnd_7303139 := by exact prefixLift 7303139
  have htrace : WordTrace (prefixWord ++ tailWord_7303139) baseStart_7303139 baseEnd_7303139 := by
    simpa [prefixWord, tailWord_7303139, baseEnd_7303139] using wordTrace_append hprefix tailTrace_7303139
  have hstable : (prefixWord ++ tailWord_7303139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303139).length < 2 ^ (prefixWord ++ tailWord_7303139).sum := by decide
  have hdescent : baseEnd_7303139 < baseStart_7303139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303169 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_7303169 : Nat := 118140960795 + 7303169 * 2 ^ 59
def prefixEnd_7303169 : Nat := 4983230072969 + 3 ^ 40 * 7303169 * 2
def baseEnd_7303169 : Nat := 3750035998015642051400843

theorem tailTrace_7303169 : CollatzResearch.WordTrace tailWord_7303169 prefixEnd_7303169 3750035998015642051400843 := by
  unfold tailWord_7303169
  simp only [CollatzResearch.WordTrace]
  refine ⟨266368456478873469809120561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177578970985915646539413707 266368456478873469809120561)
  ·
    refine ⟨199776342359155102356840421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266368456478873469809120561 199776342359155102356840421)
    ·
      refine ⟨37458064192341581691907579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199776342359155102356840421 37458064192341581691907579)
      ·
        refine ⟨56187096288512372537861369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37458064192341581691907579 56187096288512372537861369)
        ·
          refine ⟨42140322216384279403396027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56187096288512372537861369 42140322216384279403396027)
          ·
            refine ⟨63210483324576419105094041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42140322216384279403396027 63210483324576419105094041)
            ·
              refine ⟨47407862493432314328820531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63210483324576419105094041 47407862493432314328820531)
              ·
                refine ⟨71111793740148471493230797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47407862493432314328820531 71111793740148471493230797)
                ·
                  refine ⟨26666922652555676809961549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71111793740148471493230797 26666922652555676809961549)
                  ·
                    refine ⟨10000095994708378803735581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26666922652555676809961549 10000095994708378803735581)
                    ·
                      refine ⟨3750035998015642051400843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000095994708378803735581 3750035998015642051400843)
                      ·
                        rfl

theorem cell23_7303169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_7303169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303169 prefixEnd_7303169 := by exact prefixLift 7303169
  have htrace : WordTrace (prefixWord ++ tailWord_7303169) baseStart_7303169 baseEnd_7303169 := by
    simpa [prefixWord, tailWord_7303169, baseEnd_7303169] using wordTrace_append hprefix tailTrace_7303169
  have hstable : (prefixWord ++ tailWord_7303169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303169).length < 2 ^ (prefixWord ++ tailWord_7303169).sum := by decide
  have hdescent : baseEnd_7303169 < baseStart_7303169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303174 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7303174 : Nat := 118140960795 + 7303174 * 2 ^ 59
def prefixEnd_7303174 : Nat := 4983230072969 + 3 ^ 40 * 7303174 * 2
def baseEnd_7303174 : Nat := 3750038565418914531838321

theorem tailTrace_7303174 : CollatzResearch.WordTrace tailWord_7303174 prefixEnd_7303174 3750038565418914531838321 := by
  unfold tailWord_7303174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8324019963870479864470393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177579092562570237108701717 8324019963870479864470393)
  ·
    refine ⟨6243014972902859898352795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8324019963870479864470393 6243014972902859898352795)
    ·
      refine ⟨9364522459354289847529193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243014972902859898352795 9364522459354289847529193)
      ·
        refine ⟨7023391844515717385646895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364522459354289847529193 7023391844515717385646895)
        ·
          refine ⟨10535087766773576078470343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023391844515717385646895 10535087766773576078470343)
          ·
            refine ⟨15802631650160364117705515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535087766773576078470343 15802631650160364117705515)
            ·
              refine ⟨23703947475240546176558273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15802631650160364117705515 23703947475240546176558273)
              ·
                refine ⟨17777960606430409632418705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23703947475240546176558273 17777960606430409632418705)
                ·
                  refine ⟨13333470454822807224314029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17777960606430409632418705 13333470454822807224314029)
                  ·
                    refine ⟨5000051420558552709117761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13333470454822807224314029 5000051420558552709117761)
                    ·
                      refine ⟨3750038565418914531838321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000051420558552709117761 3750038565418914531838321)
                      ·
                        rfl

theorem cell23_7303174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7303174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303174 prefixEnd_7303174 := by exact prefixLift 7303174
  have htrace : WordTrace (prefixWord ++ tailWord_7303174) baseStart_7303174 baseEnd_7303174 := by
    simpa [prefixWord, tailWord_7303174, baseEnd_7303174] using wordTrace_append hprefix tailTrace_7303174
  have hstable : (prefixWord ++ tailWord_7303174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303174).length < 2 ^ (prefixWord ++ tailWord_7303174).sum := by decide
  have hdescent : baseEnd_7303174 < baseStart_7303174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303181 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7303181 : Nat := 118140960795 + 7303181 * 2 ^ 59
def prefixEnd_7303181 : Nat := 4983230072969 + 3 ^ 40 * 7303181 * 2
def baseEnd_7303181 : Nat := 3750042159783496004450789

theorem tailTrace_7303181 : CollatzResearch.WordTrace tailWord_7303181 prefixEnd_7303181 3750042159783496004450789 := by
  unfold tailWord_7303181
  simp only [CollatzResearch.WordTrace]
  refine ⟨266368894154829995858557397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177579262769886663905704931 266368894154829995858557397)
  ·
    refine ⟨6243020956753828027934939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 266368894154829995858557397 6243020956753828027934939)
    ·
      refine ⟨9364531435130742041902409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243020956753828027934939 9364531435130742041902409)
      ·
        refine ⟨7023398576348056531426807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364531435130742041902409 7023398576348056531426807)
        ·
          refine ⟨10535097864522084797140211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023398576348056531426807 10535097864522084797140211)
          ·
            refine ⟨15802646796783127195710317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535097864522084797140211 15802646796783127195710317)
            ·
              refine ⟨5925992548793672698391369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15802646796783127195710317 5925992548793672698391369)
              ·
                refine ⟨4444494411595254523793527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925992548793672698391369 4444494411595254523793527)
                ·
                  refine ⟨6666741617392881785690291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444494411595254523793527 6666741617392881785690291)
                  ·
                    refine ⟨10000112426089322678535437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666741617392881785690291 10000112426089322678535437)
                    ·
                      refine ⟨3750042159783496004450789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000112426089322678535437 3750042159783496004450789)
                      ·
                        rfl

theorem cell23_7303181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7303181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303181 prefixEnd_7303181 := by exact prefixLift 7303181
  have htrace : WordTrace (prefixWord ++ tailWord_7303181) baseStart_7303181 baseEnd_7303181 := by
    simpa [prefixWord, tailWord_7303181, baseEnd_7303181] using wordTrace_append hprefix tailTrace_7303181
  have hstable : (prefixWord ++ tailWord_7303181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303181).length < 2 ^ (prefixWord ++ tailWord_7303181).sum := by decide
  have hdescent : baseEnd_7303181 < baseStart_7303181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303207 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7303207 : Nat := 118140960795 + 7303207 * 2 ^ 59
def prefixEnd_7303207 : Nat := 4983230072969 + 3 ^ 40 * 7303207 * 2
def baseEnd_7303207 : Nat := 3750055510280512902725669

theorem tailTrace_7303207 : CollatzResearch.WordTrace tailWord_7303207 prefixEnd_7303207 3750055510280512902725669 := by
  unfold tailWord_7303207
  simp only [CollatzResearch.WordTrace]
  refine ⟨266369842452735802299003875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177579894968490534866002583 266369842452735802299003875)
  ·
    refine ⟨399554763679103703448505813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266369842452735802299003875 399554763679103703448505813)
    ·
      refine ⟨9364564773728993049574355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 399554763679103703448505813 9364564773728993049574355)
      ·
        refine ⟨14046847160593489574361533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364564773728993049574355 14046847160593489574361533)
        ·
          refine ⟨5267567685222558590385575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14046847160593489574361533 5267567685222558590385575)
          ·
            refine ⟨7901351527833837885578363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267567685222558590385575 7901351527833837885578363)
            ·
              refine ⟨11852027291750756828367545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901351527833837885578363 11852027291750756828367545)
              ·
                refine ⟨8889020468813067621275659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11852027291750756828367545 8889020468813067621275659)
                ·
                  refine ⟨13333530703219601431913489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889020468813067621275659 13333530703219601431913489)
                  ·
                    refine ⟨10000148027414701073935117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13333530703219601431913489 10000148027414701073935117)
                    ·
                      refine ⟨3750055510280512902725669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000148027414701073935117 3750055510280512902725669)
                      ·
                        rfl

theorem cell23_7303207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7303207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303207 prefixEnd_7303207 := by exact prefixLift 7303207
  have htrace : WordTrace (prefixWord ++ tailWord_7303207) baseStart_7303207 baseEnd_7303207 := by
    simpa [prefixWord, tailWord_7303207, baseEnd_7303207] using wordTrace_append hprefix tailTrace_7303207
  have hstable : (prefixWord ++ tailWord_7303207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303207).length < 2 ^ (prefixWord ++ tailWord_7303207).sum := by decide
  have hdescent : baseEnd_7303207 < baseStart_7303207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303229 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7303229 : Nat := 118140960795 + 7303229 * 2 ^ 59
def prefixEnd_7303229 : Nat := 4983230072969 + 3 ^ 40 * 7303229 * 2
def baseEnd_7303229 : Nat := 3750066806854911816650567

theorem tailTrace_7303229 : CollatzResearch.WordTrace tailWord_7303229 prefixEnd_7303229 3750066806854911816650567 := by
  unfold tailWord_7303229
  simp only [CollatzResearch.WordTrace]
  refine ⟨266370644858656100056304741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177580429905770733370869827 266370644858656100056304741)
  ·
    refine ⟨49944495910998018760557139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266370644858656100056304741 49944495910998018760557139)
    ·
      refine ⟨74916743866497028140835709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49944495910998018760557139 74916743866497028140835709)
      ·
        refine ⟨28093778949936385552813391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74916743866497028140835709 28093778949936385552813391)
        ·
          refine ⟨42140668424904578329220087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093778949936385552813391 42140668424904578329220087)
          ·
            refine ⟨63211002637356867493830131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42140668424904578329220087 63211002637356867493830131)
            ·
              refine ⟨94816503956035301240745197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63211002637356867493830131 94816503956035301240745197)
              ·
                refine ⟨35556188983513237965279449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94816503956035301240745197 35556188983513237965279449)
                ·
                  refine ⟨26667141737634928473959587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35556188983513237965279449 26667141737634928473959587)
                  ·
                    refine ⟨40000712606452392710939381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26667141737634928473959587 40000712606452392710939381)
                    ·
                      refine ⟨3750066806854911816650567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40000712606452392710939381 3750066806854911816650567)
                      ·
                        rfl

theorem cell23_7303229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7303229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303229 prefixEnd_7303229 := by exact prefixLift 7303229
  have htrace : WordTrace (prefixWord ++ tailWord_7303229) baseStart_7303229 baseEnd_7303229 := by
    simpa [prefixWord, tailWord_7303229, baseEnd_7303229] using wordTrace_append hprefix tailTrace_7303229
  have hstable : (prefixWord ++ tailWord_7303229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303229).length < 2 ^ (prefixWord ++ tailWord_7303229).sum := by decide
  have hdescent : baseEnd_7303229 < baseStart_7303229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303239 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_7303239 : Nat := 118140960795 + 7303239 * 2 ^ 59
def prefixEnd_7303239 : Nat := 4983230072969 + 3 ^ 40 * 7303239 * 2
def baseEnd_7303239 : Nat := 3750071941661456777525521

theorem tailTrace_7303239 : CollatzResearch.WordTrace tailWord_7303239 prefixEnd_7303239 3750071941661456777525521 := by
  unfold tailWord_7303239
  simp only [CollatzResearch.WordTrace]
  refine ⟨266371009588619871764168771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177580673059079914509445847 266371009588619871764168771)
  ·
    refine ⟨399556514382929807646253157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266371009588619871764168771 399556514382929807646253157)
    ·
      refine ⟨74916846446799338933672467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399556514382929807646253157 74916846446799338933672467)
      ·
        refine ⟨112375269670199008400508701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74916846446799338933672467 112375269670199008400508701)
        ·
          refine ⟨42140726126324628150190763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112375269670199008400508701 42140726126324628150190763)
          ·
            refine ⟨63211089189486942225286145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42140726126324628150190763 63211089189486942225286145)
            ·
              refine ⟨47408316892115206668964609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63211089189486942225286145 47408316892115206668964609)
              ·
                refine ⟨35556237669086405001723457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47408316892115206668964609 35556237669086405001723457)
                ·
                  refine ⟨26667178251814803751292593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35556237669086405001723457 26667178251814803751292593)
                  ·
                    refine ⟨20000383688861102813469445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26667178251814803751292593 20000383688861102813469445)
                    ·
                      refine ⟨3750071941661456777525521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20000383688861102813469445 3750071941661456777525521)
                      ·
                        rfl

theorem cell23_7303239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_7303239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303239 prefixEnd_7303239 := by exact prefixLift 7303239
  have htrace : WordTrace (prefixWord ++ tailWord_7303239) baseStart_7303239 baseEnd_7303239 := by
    simpa [prefixWord, tailWord_7303239, baseEnd_7303239] using wordTrace_append hprefix tailTrace_7303239
  have hstable : (prefixWord ++ tailWord_7303239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303239).length < 2 ^ (prefixWord ++ tailWord_7303239).sum := by decide
  have hdescent : baseEnd_7303239 < baseStart_7303239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303260 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_7303260 : Nat := 118140960795 + 7303260 * 2 ^ 59
def prefixEnd_7303260 : Nat := 4983230072969 + 3 ^ 40 * 7303260 * 2
def baseEnd_7303260 : Nat := 3750082724755201195362925

theorem tailTrace_7303260 : CollatzResearch.WordTrace tailWord_7303260 prefixEnd_7303260 3750082724755201195362925 := by
  unfold tailWord_7303260
  simp only [CollatzResearch.WordTrace]
  refine ⟨133185887760771896175341617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177581183681029194900455489 133185887760771896175341617)
  ·
    refine ⟨99889415820578922131506213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133185887760771896175341617 99889415820578922131506213)
    ·
      refine ⟨18729265466358547899657415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99889415820578922131506213 18729265466358547899657415)
      ·
        refine ⟨28093898199537821849486123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18729265466358547899657415 28093898199537821849486123)
        ·
          refine ⟨42140847299306732774229185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093898199537821849486123 42140847299306732774229185)
          ·
            refine ⟨31605635474480049580671889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42140847299306732774229185 31605635474480049580671889)
            ·
              refine ⟨23704226605860037185503917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31605635474480049580671889 23704226605860037185503917)
              ·
                refine ⟨8889084977197513944563969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23704226605860037185503917 8889084977197513944563969)
                ·
                  refine ⟨6666813732898135458422977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8889084977197513944563969 6666813732898135458422977)
                  ·
                    refine ⟨5000110299673601593817233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6666813732898135458422977 5000110299673601593817233)
                    ·
                      refine ⟨3750082724755201195362925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000110299673601593817233 3750082724755201195362925)
                      ·
                        rfl

theorem cell23_7303260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_7303260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303260 prefixEnd_7303260 := by exact prefixLift 7303260
  have htrace : WordTrace (prefixWord ++ tailWord_7303260) baseStart_7303260 baseEnd_7303260 := by
    simpa [prefixWord, tailWord_7303260, baseEnd_7303260] using wordTrace_append hprefix tailTrace_7303260
  have hstable : (prefixWord ++ tailWord_7303260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303260).length < 2 ^ (prefixWord ++ tailWord_7303260).sum := by decide
  have hdescent : baseEnd_7303260 < baseStart_7303260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303279 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 7]
def baseStart_7303279 : Nat := 118140960795 + 7303279 * 2 ^ 59
def prefixEnd_7303279 : Nat := 4983230072969 + 3 ^ 40 * 7303279 * 2
def baseEnd_7303279 : Nat := 1250030826962545540341779

theorem tailTrace_7303279 : CollatzResearch.WordTrace tailWord_7303279 prefixEnd_7303279 1250030826962545540341779 := by
  unfold tailWord_7303279
  simp only [CollatzResearch.WordTrace]
  refine ⟨266372468508474958595624891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177581645672316639063749927 266372468508474958595624891)
  ·
    refine ⟨399558702762712437893437337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266372468508474958595624891 399558702762712437893437337)
    ·
      refine ⟨299669027072034328420078003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399558702762712437893437337 299669027072034328420078003)
      ·
        refine ⟨449503540608051492630117005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299669027072034328420078003 449503540608051492630117005)
        ·
          refine ⟨168563827728019309736293877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449503540608051492630117005 168563827728019309736293877)
          ·
            refine ⟨15802858849501810287777551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168563827728019309736293877 15802858849501810287777551)
            ·
              refine ⟨23704288274252715431666327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15802858849501810287777551 23704288274252715431666327)
              ·
                refine ⟨35556432411379073147499491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23704288274252715431666327 35556432411379073147499491)
                ·
                  refine ⟨53334648617068609721249237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35556432411379073147499491 53334648617068609721249237)
                  ·
                    refine ⟨1250030826962545540341779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53334648617068609721249237 1250030826962545540341779)
                    ·
                      rfl

theorem cell23_7303279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_7303279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303279 prefixEnd_7303279 := by exact prefixLift 7303279
  have htrace : WordTrace (prefixWord ++ tailWord_7303279) baseStart_7303279 baseEnd_7303279 := by
    simpa [prefixWord, tailWord_7303279, baseEnd_7303279] using wordTrace_append hprefix tailTrace_7303279
  have hstable : (prefixWord ++ tailWord_7303279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303279).length < 2 ^ (prefixWord ++ tailWord_7303279).sum := by decide
  have hdescent : baseEnd_7303279 < baseStart_7303279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303403 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 1, 5]
def baseStart_7303403 : Nat := 118140960795 + 7303403 * 2 ^ 59
def prefixEnd_7303403 : Nat := 4983230072969 + 3 ^ 40 * 7303403 * 2
def baseEnd_7303403 : Nat := 1250052050829598045291589

theorem tailTrace_7303403 : CollatzResearch.WordTrace tailWord_7303403 prefixEnd_7303403 1250052050829598045291589 := by
  unfold tailWord_7303403
  simp only [CollatzResearch.WordTrace]
  refine ⟨266376991160025727773138863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177584660773350485182092575 266376991160025727773138863)
  ·
    refine ⟨399565486740038591659708295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266376991160025727773138863 399565486740038591659708295)
    ·
      refine ⟨599348230110057887489562443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399565486740038591659708295 599348230110057887489562443)
      ·
        refine ⟨899022345165086831234343665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599348230110057887489562443 899022345165086831234343665)
        ·
          refine ⟨674266758873815123425757749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899022345165086831234343665 674266758873815123425757749)
          ·
            refine ⟨63212508644420167821164789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 674266758873815123425757749 63212508644420167821164789)
            ·
              refine ⟨5926172685414390733234199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63212508644420167821164789 5926172685414390733234199)
              ·
                refine ⟨8889259028121586099851299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926172685414390733234199 8889259028121586099851299)
                ·
                  refine ⟨13333888542182379149776949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889259028121586099851299 13333888542182379149776949)
                  ·
                    refine ⟨1250052050829598045291589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13333888542182379149776949 1250052050829598045291589)
                    ·
                      rfl

theorem cell23_7303403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 5].length) (baseStart_7303403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303403 prefixEnd_7303403 := by exact prefixLift 7303403
  have htrace : WordTrace (prefixWord ++ tailWord_7303403) baseStart_7303403 baseEnd_7303403 := by
    simpa [prefixWord, tailWord_7303403, baseEnd_7303403] using wordTrace_append hprefix tailTrace_7303403
  have hstable : (prefixWord ++ tailWord_7303403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303403).length < 2 ^ (prefixWord ++ tailWord_7303403).sum := by decide
  have hdescent : baseEnd_7303403 < baseStart_7303403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303410 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7303410 : Nat := 118140960795 + 7303410 * 2 ^ 59
def prefixEnd_7303410 : Nat := 4983230072969 + 3 ^ 40 * 7303410 * 2
def baseEnd_7303410 : Nat := 3750159746853375608487235

theorem tailTrace_7303410 : CollatzResearch.WordTrace tailWord_7303410 prefixEnd_7303410 3750159746853375608487235 := by
  unfold tailWord_7303410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66594311617750091992160921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177584830980666911979095789 66594311617750091992160921)
  ·
    refine ⟨49945733713312568994120691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66594311617750091992160921 49945733713312568994120691)
    ·
      refine ⟨74918600569968853491181037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49945733713312568994120691 74918600569968853491181037)
      ·
        refine ⟨28094475213738320059192889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74918600569968853491181037 28094475213738320059192889)
        ·
          refine ⟨21070856410303740044394667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28094475213738320059192889 21070856410303740044394667)
          ·
            refine ⟨31606284615455610066592001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21070856410303740044394667 31606284615455610066592001)
            ·
              refine ⟨23704713461591707549944001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31606284615455610066592001 23704713461591707549944001)
              ·
                refine ⟨17778535096193780662458001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23704713461591707549944001 17778535096193780662458001)
                ·
                  refine ⟨13333901322145335496843501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17778535096193780662458001 13333901322145335496843501)
                  ·
                    refine ⟨5000212995804500811316313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13333901322145335496843501 5000212995804500811316313)
                    ·
                      refine ⟨3750159746853375608487235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000212995804500811316313 3750159746853375608487235)
                      ·
                        rfl

theorem cell23_7303410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7303410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303410 prefixEnd_7303410 := by exact prefixLift 7303410
  have htrace : WordTrace (prefixWord ++ tailWord_7303410) baseStart_7303410 baseEnd_7303410 := by
    simpa [prefixWord, tailWord_7303410, baseEnd_7303410] using wordTrace_append hprefix tailTrace_7303410
  have hstable : (prefixWord ++ tailWord_7303410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303410).length < 2 ^ (prefixWord ++ tailWord_7303410).sum := by decide
  have hdescent : baseEnd_7303410 < baseStart_7303410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303416 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_7303416 : Nat := 118140960795 + 7303416 * 2 ^ 59
def prefixEnd_7303416 : Nat := 4983230072969 + 3 ^ 40 * 7303416 * 2
def baseEnd_7303416 : Nat := 1250054275912434195004069

theorem tailTrace_7303416 : CollatzResearch.WordTrace tailWord_7303416 prefixEnd_7303416 1250054275912434195004069 := by
  unfold tailWord_7303416
  simp only [CollatzResearch.WordTrace]
  refine ⟨133188732654489315496681051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177584976872652420662241401 133188732654489315496681051)
  ·
    refine ⟨199783098981733973245021577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133188732654489315496681051 199783098981733973245021577)
    ·
      refine ⟨149837324236300479933766183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199783098981733973245021577 149837324236300479933766183)
      ·
        refine ⟨224755986354450719900649275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149837324236300479933766183 224755986354450719900649275)
        ·
          refine ⟨337133979531676079850973913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224755986354450719900649275 337133979531676079850973913)
          ·
            refine ⟨252850484648757059888230435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337133979531676079850973913 252850484648757059888230435)
            ·
              refine ⟨379275726973135589832345653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252850484648757059888230435 379275726973135589832345653)
              ·
                refine ⟨35557099403731461546782405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379275726973135589832345653 35557099403731461546782405)
                ·
                  refine ⟨6666956138199649040021701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35557099403731461546782405 6666956138199649040021701)
                  ·
                    refine ⟨1250054275912434195004069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6666956138199649040021701 1250054275912434195004069)
                    ·
                      rfl

theorem cell23_7303416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_7303416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303416 prefixEnd_7303416 := by exact prefixLift 7303416
  have htrace : WordTrace (prefixWord ++ tailWord_7303416) baseStart_7303416 baseEnd_7303416 := by
    simpa [prefixWord, tailWord_7303416, baseEnd_7303416] using wordTrace_append hprefix tailTrace_7303416
  have hstable : (prefixWord ++ tailWord_7303416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303416).length < 2 ^ (prefixWord ++ tailWord_7303416).sum := by decide
  have hdescent : baseEnd_7303416 < baseStart_7303416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303429 : List Nat := [1, 3, 1, 1, 2, 1, 2, 12]
def baseStart_7303429 : Nat := 118140960795 + 7303429 * 2 ^ 59
def prefixEnd_7303429 : Nat := 4983230072969 + 3 ^ 40 * 7303429 * 2
def baseEnd_7303429 : Nat := 138895166777252260524061

theorem tailTrace_7303429 : CollatzResearch.WordTrace tailWord_7303429 prefixEnd_7303429 138895166777252260524061 := by
  unfold tailWord_7303429
  simp only [CollatzResearch.WordTrace]
  refine ⟨266377939457931534213585341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177585292971954356142390227 266377939457931534213585341)
  ·
    refine ⟨99891727296724325330094503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266377939457931534213585341 99891727296724325330094503)
    ·
      refine ⟨149837590945086487995141755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99891727296724325330094503 149837590945086487995141755)
      ·
        refine ⟨224756386417629731992712633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149837590945086487995141755 224756386417629731992712633)
        ·
          refine ⟨168567289813222298994534475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224756386417629731992712633 168567289813222298994534475)
          ·
            refine ⟨252850934719833448491801713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168567289813222298994534475 252850934719833448491801713)
            ·
              refine ⟨189638201039875086368851285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252850934719833448491801713 189638201039875086368851285)
              ·
                refine ⟨138895166777252260524061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 189638201039875086368851285 138895166777252260524061)
                ·
                  rfl

theorem cell23_7303429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 12].length) (baseStart_7303429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303429 prefixEnd_7303429 := by exact prefixLift 7303429
  have htrace : WordTrace (prefixWord ++ tailWord_7303429) baseStart_7303429 baseEnd_7303429 := by
    simpa [prefixWord, tailWord_7303429, baseEnd_7303429] using wordTrace_append hprefix tailTrace_7303429
  have hstable : (prefixWord ++ tailWord_7303429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303429).length < 2 ^ (prefixWord ++ tailWord_7303429).sum := by decide
  have hdescent : baseEnd_7303429 < baseStart_7303429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303433 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_7303433 : Nat := 118140960795 + 7303433 * 2 ^ 59
def prefixEnd_7303433 : Nat := 4983230072969 + 3 ^ 40 * 7303433 * 2
def baseEnd_7303433 : Nat := 1250057185636143006166543

theorem tailTrace_7303433 : CollatzResearch.WordTrace tailWord_7303433 prefixEnd_7303433 1250057185636143006166543 := by
  unfold tailWord_7303433
  simp only [CollatzResearch.WordTrace]
  refine ⟨266378085349917042896730953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177585390233278028597820635 266378085349917042896730953)
  ·
    refine ⟨199783564012437782172548215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266378085349917042896730953 199783564012437782172548215)
    ·
      refine ⟨299675346018656673258822323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199783564012437782172548215 299675346018656673258822323)
      ·
        refine ⟨449513019027985009888233485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299675346018656673258822323 449513019027985009888233485)
        ·
          refine ⟨168567382135494378708087557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449513019027985009888233485 168567382135494378708087557)
          ·
            refine ⟨31606384150405196007766417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168567382135494378708087557 31606384150405196007766417)
            ·
              refine ⟨23704788112803897005824813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31606384150405196007766417 23704788112803897005824813)
              ·
                refine ⟨8889295542301461377184305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23704788112803897005824813 8889295542301461377184305)
                ·
                  refine ⟨6666971656726096032888229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8889295542301461377184305 6666971656726096032888229)
                  ·
                    refine ⟨1250057185636143006166543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6666971656726096032888229 1250057185636143006166543)
                    ·
                      rfl

theorem cell23_7303433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_7303433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303433 prefixEnd_7303433 := by exact prefixLift 7303433
  have htrace : WordTrace (prefixWord ++ tailWord_7303433) baseStart_7303433 baseEnd_7303433 := by
    simpa [prefixWord, tailWord_7303433, baseEnd_7303433] using wordTrace_append hprefix tailTrace_7303433
  have hstable : (prefixWord ++ tailWord_7303433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303433).length < 2 ^ (prefixWord ++ tailWord_7303433).sum := by decide
  have hdescent : baseEnd_7303433 < baseStart_7303433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303439 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_7303439 : Nat := 118140960795 + 7303439 * 2 ^ 59
def prefixEnd_7303439 : Nat := 4983230072969 + 3 ^ 40 * 7303439 * 2
def baseEnd_7303439 : Nat := 3750174637792355995024601

theorem tailTrace_7303439 : CollatzResearch.WordTrace tailWord_7303439 prefixEnd_7303439 3750174637792355995024601 := by
  unfold tailWord_7303439
  simp only [CollatzResearch.WordTrace]
  refine ⟨266378304187895305921449371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177585536125263537280966247 266378304187895305921449371)
  ·
    refine ⟨399567456281842958882174057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266378304187895305921449371 399567456281842958882174057)
    ·
      refine ⟨299675592211382219161630543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399567456281842958882174057 299675592211382219161630543)
      ·
        refine ⟨449513388317073328742445815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299675592211382219161630543 449513388317073328742445815)
        ·
          refine ⟨674270082475609993113668723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449513388317073328742445815 674270082475609993113668723)
          ·
            refine ⟨1011405123713414989670503085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674270082475609993113668723 1011405123713414989670503085)
            ·
              refine ⟨379276921392530621126438657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1011405123713414989670503085 379276921392530621126438657)
              ·
                refine ⟨284457691044397965844828993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379276921392530621126438657 284457691044397965844828993)
                ·
                  refine ⟨213343268283298474383621745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284457691044397965844828993 213343268283298474383621745)
                  ·
                    refine ⟨160007451212473855787716309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213343268283298474383621745 160007451212473855787716309)
                    ·
                      refine ⟨3750174637792355995024601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160007451212473855787716309 3750174637792355995024601)
                      ·
                        rfl

theorem cell23_7303439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_7303439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303439 prefixEnd_7303439 := by exact prefixLift 7303439
  have htrace : WordTrace (prefixWord ++ tailWord_7303439) baseStart_7303439 baseEnd_7303439 := by
    simpa [prefixWord, tailWord_7303439, baseEnd_7303439] using wordTrace_append hprefix tailTrace_7303439
  have hstable : (prefixWord ++ tailWord_7303439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303439).length < 2 ^ (prefixWord ++ tailWord_7303439).sum := by decide
  have hdescent : baseEnd_7303439 < baseStart_7303439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303454 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7303454 : Nat := 118140960795 + 7303454 * 2 ^ 59
def prefixEnd_7303454 : Nat := 4983230072969 + 3 ^ 40 * 7303454 * 2
def baseEnd_7303454 : Nat := 1250060780000724478779011

theorem tailTrace_7303454 : CollatzResearch.WordTrace tailWord_7303454 prefixEnd_7303454 1250060780000724478779011 := by
  unfold tailWord_7303454
  simp only [CollatzResearch.WordTrace]
  refine ⟨33297356410355120435405677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177585900855227308988830277 33297356410355120435405677)
  ·
    refine ⟨12486508653883170163277129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33297356410355120435405677 12486508653883170163277129)
    ·
      refine ⟨9364881490412377622457847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12486508653883170163277129 9364881490412377622457847)
      ·
        refine ⟨14047322235618566433686771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364881490412377622457847 14047322235618566433686771)
        ·
          refine ⟨21070983353427849650530157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14047322235618566433686771 21070983353427849650530157)
          ·
            refine ⟨7901618757535443618948809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21070983353427849650530157 7901618757535443618948809)
            ·
              refine ⟨5926214068151582714211607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901618757535443618948809 5926214068151582714211607)
              ·
                refine ⟨8889321102227374071317411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926214068151582714211607 8889321102227374071317411)
                ·
                  refine ⟨13333981653341061106976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889321102227374071317411 13333981653341061106976117)
                  ·
                    refine ⟨1250060780000724478779011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13333981653341061106976117 1250060780000724478779011)
                    ·
                      rfl

theorem cell23_7303454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7303454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303454 prefixEnd_7303454 := by exact prefixLift 7303454
  have htrace : WordTrace (prefixWord ++ tailWord_7303454) baseStart_7303454 baseEnd_7303454 := by
    simpa [prefixWord, tailWord_7303454, baseEnd_7303454] using wordTrace_append hprefix tailTrace_7303454
  have hstable : (prefixWord ++ tailWord_7303454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303454).length < 2 ^ (prefixWord ++ tailWord_7303454).sum := by decide
  have hdescent : baseEnd_7303454 < baseStart_7303454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303457 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_7303457 : Nat := 118140960795 + 7303457 * 2 ^ 59
def prefixEnd_7303457 : Nat := 4983230072969 + 3 ^ 40 * 7303457 * 2
def baseEnd_7303457 : Nat := 3750183880444136924599519

theorem tailTrace_7303457 : CollatzResearch.WordTrace tailWord_7303457 prefixEnd_7303457 3750183880444136924599519 := by
  unfold tailWord_7303457
  simp only [CollatzResearch.WordTrace]
  refine ⟨266378960701830094995604625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177585973801220063330403083 266378960701830094995604625)
  ·
    refine ⟨199784220526372571246703469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266378960701830094995604625 199784220526372571246703469)
    ·
      refine ⟨74919082697389714217513801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199784220526372571246703469 74919082697389714217513801)
      ·
        refine ⟨56189312023042285663135351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74919082697389714217513801 56189312023042285663135351)
        ·
          refine ⟨84283968034563428494703027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56189312023042285663135351 84283968034563428494703027)
          ·
            refine ⟨126425952051845142742054541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84283968034563428494703027 126425952051845142742054541)
            ·
              refine ⟨47409732019441928528270453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126425952051845142742054541 47409732019441928528270453)
              ·
                refine ⟨4444662376822680799525355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47409732019441928528270453 4444662376822680799525355)
                ·
                  refine ⟨6666993565234021199288033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444662376822680799525355 6666993565234021199288033)
                  ·
                    refine ⟨5000245173925515899466025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6666993565234021199288033 5000245173925515899466025)
                    ·
                      refine ⟨3750183880444136924599519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000245173925515899466025 3750183880444136924599519)
                      ·
                        rfl

theorem cell23_7303457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_7303457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303457 prefixEnd_7303457 := by exact prefixLift 7303457
  have htrace : WordTrace (prefixWord ++ tailWord_7303457) baseStart_7303457 baseEnd_7303457 := by
    simpa [prefixWord, tailWord_7303457, baseEnd_7303457] using wordTrace_append hprefix tailTrace_7303457
  have hstable : (prefixWord ++ tailWord_7303457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303457).length < 2 ^ (prefixWord ++ tailWord_7303457).sum := by decide
  have hdescent : baseEnd_7303457 < baseStart_7303457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303460 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_7303460 : Nat := 118140960795 + 7303460 * 2 ^ 59
def prefixEnd_7303460 : Nat := 4983230072969 + 3 ^ 40 * 7303460 * 2
def baseEnd_7303460 : Nat := 3750185420886100412862005

theorem tailTrace_7303460 : CollatzResearch.WordTrace tailWord_7303460 prefixEnd_7303460 3750185420886100412862005 := by
  unfold tailWord_7303460
  simp only [CollatzResearch.WordTrace]
  refine ⟨133189535060409613253981917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177586046747212817671975889 133189535060409613253981917)
  ·
    refine ⟨49946075647653604970243219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133189535060409613253981917 49946075647653604970243219)
    ·
      refine ⟨74919113471480407455364829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49946075647653604970243219 74919113471480407455364829)
      ·
        refine ⟨28094667551805152795761811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74919113471480407455364829 28094667551805152795761811)
        ·
          refine ⟨42142001327707729193642717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28094667551805152795761811 42142001327707729193642717)
          ·
            refine ⟨15803250497890398447616019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42142001327707729193642717 15803250497890398447616019)
            ·
              refine ⟨23704875746835597671424029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803250497890398447616019 23704875746835597671424029)
              ·
                refine ⟨8889328405063349126784011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23704875746835597671424029 8889328405063349126784011)
                ·
                  refine ⟨13333992607595023690176017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889328405063349126784011 13333992607595023690176017)
                  ·
                    refine ⟨10000494455696267767632013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13333992607595023690176017 10000494455696267767632013)
                    ·
                      refine ⟨3750185420886100412862005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000494455696267767632013 3750185420886100412862005)
                      ·
                        rfl

theorem cell23_7303460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_7303460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303460 prefixEnd_7303460 := by exact prefixLift 7303460
  have htrace : WordTrace (prefixWord ++ tailWord_7303460) baseStart_7303460 baseEnd_7303460 := by
    simpa [prefixWord, tailWord_7303460, baseEnd_7303460] using wordTrace_append hprefix tailTrace_7303460
  have hstable : (prefixWord ++ tailWord_7303460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303460).length < 2 ^ (prefixWord ++ tailWord_7303460).sum := by decide
  have hdescent : baseEnd_7303460 < baseStart_7303460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303496 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7303496 : Nat := 118140960795 + 7303496 * 2 ^ 59
def prefixEnd_7303496 : Nat := 4983230072969 + 3 ^ 40 * 7303496 * 2
def baseEnd_7303496 : Nat := 3750203906189662272011839

theorem tailTrace_7303496 : CollatzResearch.WordTrace tailWord_7303496 prefixEnd_7303496 3750203906189662272011839 := by
  unfold tailWord_7303496
  simp only [CollatzResearch.WordTrace]
  refine ⟨133190191574344402328137171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177586922099125869770849561 133190191574344402328137171)
  ·
    refine ⟨199785287361516603492205757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133190191574344402328137171 199785287361516603492205757)
    ·
      refine ⟨74919482760568726309577159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199785287361516603492205757 74919482760568726309577159)
      ·
        refine ⟨112379224140853089464365739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74919482760568726309577159 112379224140853089464365739)
        ·
          refine ⟨168568836211279634196548609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112379224140853089464365739 168568836211279634196548609)
          ·
            refine ⟨126426627158459725647411457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168568836211279634196548609 126426627158459725647411457)
            ·
              refine ⟨94819970368844794235558593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126426627158459725647411457 94819970368844794235558593)
              ·
                refine ⟨71114977776633595676668945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94819970368844794235558593 71114977776633595676668945)
                ·
                  refine ⟨53336233332475196757501709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71114977776633595676668945 53336233332475196757501709)
                  ·
                    refine ⟨20001087499678198784063141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53336233332475196757501709 20001087499678198784063141)
                    ·
                      refine ⟨3750203906189662272011839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20001087499678198784063141 3750203906189662272011839)
                      ·
                        rfl

theorem cell23_7303496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7303496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303496 prefixEnd_7303496 := by exact prefixLift 7303496
  have htrace : WordTrace (prefixWord ++ tailWord_7303496) baseStart_7303496 baseEnd_7303496 := by
    simpa [prefixWord, tailWord_7303496, baseEnd_7303496] using wordTrace_append hprefix tailTrace_7303496
  have hstable : (prefixWord ++ tailWord_7303496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303496).length < 2 ^ (prefixWord ++ tailWord_7303496).sum := by decide
  have hdescent : baseEnd_7303496 < baseStart_7303496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303506 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_7303506 : Nat := 118140960795 + 7303506 * 2 ^ 59
def prefixEnd_7303506 : Nat := 4983230072969 + 3 ^ 40 * 7303506 * 2
def baseEnd_7303506 : Nat := 1250069680332069077628931

theorem tailTrace_7303506 : CollatzResearch.WordTrace tailWord_7303506 prefixEnd_7303506 1250069680332069077628931 := by
  unfold tailWord_7303506
  simp only [CollatzResearch.WordTrace]
  refine ⟨66595186969663144091034593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177587165252435050909425581 66595186969663144091034593)
  ·
    refine ⟨49946390227247358068275945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66595186969663144091034593 49946390227247358068275945)
    ·
      refine ⟨37459792670435518551206959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49946390227247358068275945 37459792670435518551206959)
      ·
        refine ⟨56189689005653277826810439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37459792670435518551206959 56189689005653277826810439)
        ·
          refine ⟨84284533508479916740215659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56189689005653277826810439 84284533508479916740215659)
          ·
            refine ⟨126426800262719875110323489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84284533508479916740215659 126426800262719875110323489)
            ·
              refine ⟨94820100197039906332742617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126426800262719875110323489 94820100197039906332742617)
              ·
                refine ⟨71115075147779929749556963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94820100197039906332742617 71115075147779929749556963)
                ·
                  refine ⟨106672612721669894624335445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71115075147779929749556963 106672612721669894624335445)
                  ·
                    refine ⟨1250069680332069077628931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106672612721669894624335445 1250069680332069077628931)
                    ·
                      rfl

theorem cell23_7303506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_7303506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303506 prefixEnd_7303506 := by exact prefixLift 7303506
  have htrace : WordTrace (prefixWord ++ tailWord_7303506) baseStart_7303506 baseEnd_7303506 := by
    simpa [prefixWord, tailWord_7303506, baseEnd_7303506] using wordTrace_append hprefix tailTrace_7303506
  have hstable : (prefixWord ++ tailWord_7303506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303506).length < 2 ^ (prefixWord ++ tailWord_7303506).sum := by decide
  have hdescent : baseEnd_7303506 < baseStart_7303506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303513 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 3, 4, 2]
def baseStart_7303513 : Nat := 118140960795 + 7303513 * 2 ^ 59
def prefixEnd_7303513 : Nat := 4983230072969 + 3 ^ 40 * 7303513 * 2
def baseEnd_7303513 : Nat := 3750212635360788705499261

theorem tailTrace_7303513 : CollatzResearch.WordTrace tailWord_7303513 prefixEnd_7303513 3750212635360788705499261 := by
  unfold tailWord_7303513
  simp only [CollatzResearch.WordTrace]
  refine ⟨266381003189627216559643193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177587335459751477706428795 266381003189627216559643193)
  ·
    refine ⟨199785752392220412419732395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266381003189627216559643193 199785752392220412419732395)
    ·
      refine ⟨299678628588330618629598593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199785752392220412419732395 299678628588330618629598593)
      ·
        refine ⟨224758971441247963972198945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299678628588330618629598593 224758971441247963972198945)
        ·
          refine ⟨168569228580935972979149209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224758971441247963972198945 168569228580935972979149209)
          ·
            refine ⟨126426921435701979734361907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168569228580935972979149209 126426921435701979734361907)
            ·
              refine ⟨189640382153552969601542861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126426921435701979734361907 189640382153552969601542861)
              ·
                refine ⟨71115143307582363600578573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189640382153552969601542861 71115143307582363600578573)
                ·
                  refine ⟨26668178740343386350216965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71115143307582363600578573 26668178740343386350216965)
                  ·
                    refine ⟨5000283513814384940665681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26668178740343386350216965 5000283513814384940665681)
                    ·
                      refine ⟨3750212635360788705499261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000283513814384940665681 3750212635360788705499261)
                      ·
                        rfl

theorem cell23_7303513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_7303513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303513 prefixEnd_7303513 := by exact prefixLift 7303513
  have htrace : WordTrace (prefixWord ++ tailWord_7303513) baseStart_7303513 baseEnd_7303513 := by
    simpa [prefixWord, tailWord_7303513, baseEnd_7303513] using wordTrace_append hprefix tailTrace_7303513
  have hstable : (prefixWord ++ tailWord_7303513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303513).length < 2 ^ (prefixWord ++ tailWord_7303513).sum := by decide
  have hdescent : baseEnd_7303513 < baseStart_7303513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303533 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7303533 : Nat := 118140960795 + 7303533 * 2 ^ 59
def prefixEnd_7303533 : Nat := 4983230072969 + 3 ^ 40 * 7303533 * 2
def baseEnd_7303533 : Nat := 3750222904973878627249169

theorem tailTrace_7303533 : CollatzResearch.WordTrace tailWord_7303533 prefixEnd_7303533 3750222904973878627249169 := by
  unfold tailWord_7303533
  simp only [CollatzResearch.WordTrace]
  refine ⟨266381732649554759975371253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177587821766369839983580835 266381732649554759975371253)
  ·
    refine ⟨24973287435895758747691055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266381732649554759975371253 24973287435895758747691055)
    ·
      refine ⟨37459931153843638121536583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24973287435895758747691055 37459931153843638121536583)
      ·
        refine ⟨56189896730765457182304875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37459931153843638121536583 56189896730765457182304875)
        ·
          refine ⟨84284845096148185773457313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56189896730765457182304875 84284845096148185773457313)
          ·
            refine ⟨63213633822111139330092985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84284845096148185773457313 63213633822111139330092985)
            ·
              refine ⟨47410225366583354497569739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63213633822111139330092985 47410225366583354497569739)
              ·
                refine ⟨71115338049875031746354609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47410225366583354497569739 71115338049875031746354609)
                ·
                  refine ⟨53336503537406273809765957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71115338049875031746354609 53336503537406273809765957)
                  ·
                    refine ⟨10000594413263676339331117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53336503537406273809765957 10000594413263676339331117)
                    ·
                      refine ⟨3750222904973878627249169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000594413263676339331117 3750222904973878627249169)
                      ·
                        rfl

theorem cell23_7303533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7303533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303533 prefixEnd_7303533 := by exact prefixLift 7303533
  have htrace : WordTrace (prefixWord ++ tailWord_7303533) baseStart_7303533 baseEnd_7303533 := by
    simpa [prefixWord, tailWord_7303533, baseEnd_7303533] using wordTrace_append hprefix tailTrace_7303533
  have hstable : (prefixWord ++ tailWord_7303533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303533).length < 2 ^ (prefixWord ++ tailWord_7303533).sum := by decide
  have hdescent : baseEnd_7303533 < baseStart_7303533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303547 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 2, 2, 2]
def baseStart_7303547 : Nat := 118140960795 + 7303547 * 2 ^ 59
def prefixEnd_7303547 : Nat := 4983230072969 + 3 ^ 40 * 7303547 * 2
def baseEnd_7303547 : Nat := 3750230093703041572474105

theorem tailTrace_7303547 : CollatzResearch.WordTrace tailWord_7303547 prefixEnd_7303547 3750230093703041572474105 := by
  unfold tailWord_7303547
  simp only [CollatzResearch.WordTrace]
  refine ⟨266382243271504040366380895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177588162181002693577587263 266382243271504040366380895)
  ·
    refine ⟨399573364907256060549571343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266382243271504040366380895 399573364907256060549571343)
    ·
      refine ⟨599360047360884090824357015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399573364907256060549571343 599360047360884090824357015)
      ·
        refine ⟨899040071041326136236535523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599360047360884090824357015 899040071041326136236535523)
        ·
          refine ⟨1348560106561989204354803285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899040071041326136236535523 1348560106561989204354803285)
          ·
            refine ⟨15803438748773310988532851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1348560106561989204354803285 15803438748773310988532851)
            ·
              refine ⟨23705158123159966482799277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803438748773310988532851 23705158123159966482799277)
              ·
                refine ⟨8889434296184987431049729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23705158123159966482799277 8889434296184987431049729)
                ·
                  refine ⟨6667075722138740573287297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8889434296184987431049729 6667075722138740573287297)
                  ·
                    refine ⟨5000306791604055429965473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667075722138740573287297 5000306791604055429965473)
                    ·
                      refine ⟨3750230093703041572474105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000306791604055429965473 3750230093703041572474105)
                      ·
                        rfl

theorem cell23_7303547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2, 2].length) (baseStart_7303547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303547 prefixEnd_7303547 := by exact prefixLift 7303547
  have htrace : WordTrace (prefixWord ++ tailWord_7303547) baseStart_7303547 baseEnd_7303547 := by
    simpa [prefixWord, tailWord_7303547, baseEnd_7303547] using wordTrace_append hprefix tailTrace_7303547
  have hstable : (prefixWord ++ tailWord_7303547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303547).length < 2 ^ (prefixWord ++ tailWord_7303547).sum := by decide
  have hdescent : baseEnd_7303547 < baseStart_7303547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303583 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 2, 5]
def baseStart_7303583 : Nat := 118140960795 + 7303583 * 2 ^ 59
def prefixEnd_7303583 : Nat := 4983230072969 + 3 ^ 40 * 7303583 * 2
def baseEnd_7303583 : Nat := 1250082859668867810541313

theorem tailTrace_7303583 : CollatzResearch.WordTrace tailWord_7303583 prefixEnd_7303583 1250082859668867810541313 := by
  unfold tailWord_7303583
  simp only [CollatzResearch.WordTrace]
  refine ⟨266383556299373618514691403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177589037532915745676460935 266383556299373618514691403)
  ·
    refine ⟨399575334449060427772037105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266383556299373618514691403 399575334449060427772037105)
    ·
      refine ⟨299681500836795320829027829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399575334449060427772037105 299681500836795320829027829)
      ·
        refine ⟨28095140703449561327721359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299681500836795320829027829 28095140703449561327721359)
        ·
          refine ⟨42142711055174341991582039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28095140703449561327721359 42142711055174341991582039)
          ·
            refine ⟨63214066582761512987373059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42142711055174341991582039 63214066582761512987373059)
            ·
              refine ⟨94821099874142269481059589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63214066582761512987373059 94821099874142269481059589)
              ·
                refine ⟨17778956226401675527698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94821099874142269481059589 17778956226401675527698673)
                ·
                  refine ⟨13334217169801256645774005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17778956226401675527698673 13334217169801256645774005)
                  ·
                    refine ⟨1250082859668867810541313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13334217169801256645774005 1250082859668867810541313)
                    ·
                      rfl

theorem cell23_7303583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_7303583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303583 prefixEnd_7303583 := by exact prefixLift 7303583
  have htrace : WordTrace (prefixWord ++ tailWord_7303583) baseStart_7303583 baseEnd_7303583 := by
    simpa [prefixWord, tailWord_7303583, baseEnd_7303583] using wordTrace_append hprefix tailTrace_7303583
  have hstable : (prefixWord ++ tailWord_7303583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303583).length < 2 ^ (prefixWord ++ tailWord_7303583).sum := by decide
  have hdescent : baseEnd_7303583 < baseStart_7303583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303587 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 5]
def baseStart_7303587 : Nat := 118140960795 + 7303587 * 2 ^ 59
def prefixEnd_7303587 : Nat := 4983230072969 + 3 ^ 40 * 7303587 * 2
def baseEnd_7303587 : Nat := 416694514769913490663769

theorem tailTrace_7303587 : CollatzResearch.WordTrace tailWord_7303587 prefixEnd_7303587 416694514769913490663769 := by
  unfold tailWord_7303587
  simp only [CollatzResearch.WordTrace]
  refine ⟨266383702191359127197837015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177589134794239418131891343 266383702191359127197837015)
  ·
    refine ⟨399575553287038690796755523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266383702191359127197837015 399575553287038690796755523)
    ·
      refine ⟨599363329930558036195133285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399575553287038690796755523 599363329930558036195133285)
      ·
        refine ⟨112380624361979631786587491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599363329930558036195133285 112380624361979631786587491)
        ·
          refine ⟨168570936542969447679881237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112380624361979631786587491 168570936542969447679881237)
          ·
            refine ⟨7901762650451692859994433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168570936542969447679881237 7901762650451692859994433)
            ·
              refine ⟨5926321987838769644995825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901762650451692859994433 5926321987838769644995825)
              ·
                refine ⟨4444741490879077233746869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5926321987838769644995825 4444741490879077233746869)
                ·
                  refine ⟨416694514769913490663769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444741490879077233746869 416694514769913490663769)
                  ·
                    rfl

theorem cell23_7303587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 5].length) (baseStart_7303587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303587 prefixEnd_7303587 := by exact prefixLift 7303587
  have htrace : WordTrace (prefixWord ++ tailWord_7303587) baseStart_7303587 baseEnd_7303587 := by
    simpa [prefixWord, tailWord_7303587, baseEnd_7303587] using wordTrace_append hprefix tailTrace_7303587
  have hstable : (prefixWord ++ tailWord_7303587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303587).length < 2 ^ (prefixWord ++ tailWord_7303587).sum := by decide
  have hdescent : baseEnd_7303587 < baseStart_7303587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303594 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7303594 : Nat := 118140960795 + 7303594 * 2 ^ 59
def prefixEnd_7303594 : Nat := 4983230072969 + 3 ^ 40 * 7303594 * 2
def baseEnd_7303594 : Nat := 3750254227293802888586389

theorem tailTrace_7303594 : CollatzResearch.WordTrace tailWord_7303594 prefixEnd_7303594 3750254227293802888586389 := by
  unfold tailWord_7303594
  simp only [CollatzResearch.WordTrace]
  refine ⟨66595989375583441848335459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177589305001555844928894557 66595989375583441848335459)
  ·
    refine ⟨99893984063375162772503189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66595989375583441848335459 99893984063375162772503189)
    ·
      refine ⟨4682530502970710754961087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99893984063375162772503189 4682530502970710754961087)
      ·
        refine ⟨7023795754456066132441631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682530502970710754961087 7023795754456066132441631)
        ·
          refine ⟨10535693631684099198662447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023795754456066132441631 10535693631684099198662447)
          ·
            refine ⟨15803540447526148797993671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535693631684099198662447 15803540447526148797993671)
            ·
              refine ⟨23705310671289223196990507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803540447526148797993671 23705310671289223196990507)
              ·
                refine ⟨35557966006933834795485761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23705310671289223196990507 35557966006933834795485761)
                ·
                  refine ⟨26668474505200376096614321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35557966006933834795485761 26668474505200376096614321)
                  ·
                    refine ⟨20001355878900282072460741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26668474505200376096614321 20001355878900282072460741)
                    ·
                      refine ⟨3750254227293802888586389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20001355878900282072460741 3750254227293802888586389)
                      ·
                        rfl

theorem cell23_7303594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7303594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303594 prefixEnd_7303594 := by exact prefixLift 7303594
  have htrace : WordTrace (prefixWord ++ tailWord_7303594) baseStart_7303594 baseEnd_7303594 := by
    simpa [prefixWord, tailWord_7303594, baseEnd_7303594] using wordTrace_append hprefix tailTrace_7303594
  have hstable : (prefixWord ++ tailWord_7303594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303594).length < 2 ^ (prefixWord ++ tailWord_7303594).sum := by decide
  have hdescent : baseEnd_7303594 < baseStart_7303594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303596 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_7303596 : Nat := 118140960795 + 7303596 * 2 ^ 59
def prefixEnd_7303596 : Nat := 4983230072969 + 3 ^ 40 * 7303596 * 2
def baseEnd_7303596 : Nat := 1250085084751703960253793

theorem tailTrace_7303596 : CollatzResearch.WordTrace tailWord_7303596 prefixEnd_7303596 1250085084751703960253793 := by
  unfold tailWord_7303596
  simp only [CollatzResearch.WordTrace]
  refine ⟨133192015224163260867457321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177589353632217681156609761 133192015224163260867457321)
  ·
    refine ⟨99894011418122445650592991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133192015224163260867457321 99894011418122445650592991)
    ·
      refine ⟨149841017127183668475889487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99894011418122445650592991 149841017127183668475889487)
      ·
        refine ⟨224761525690775502713834231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149841017127183668475889487 224761525690775502713834231)
        ·
          refine ⟨337142288536163254070751347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224761525690775502713834231 337142288536163254070751347)
          ·
            refine ⟨505713432804244881106127021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337142288536163254070751347 505713432804244881106127021)
            ·
              refine ⟨189642537301591830414797633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505713432804244881106127021 189642537301591830414797633)
              ·
                refine ⟨142231902976193872811098225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189642537301591830414797633 142231902976193872811098225)
                ·
                  refine ⟨106673927232145404608323669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142231902976193872811098225 106673927232145404608323669)
                  ·
                    refine ⟨1250085084751703960253793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106673927232145404608323669 1250085084751703960253793)
                    ·
                      rfl

theorem cell23_7303596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_7303596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303596 prefixEnd_7303596 := by exact prefixLift 7303596
  have htrace : WordTrace (prefixWord ++ tailWord_7303596) baseStart_7303596 baseEnd_7303596 := by
    simpa [prefixWord, tailWord_7303596, baseEnd_7303596] using wordTrace_append hprefix tailTrace_7303596
  have hstable : (prefixWord ++ tailWord_7303596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303596).length < 2 ^ (prefixWord ++ tailWord_7303596).sum := by decide
  have hdescent : baseEnd_7303596 < baseStart_7303596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303597 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7303597 : Nat := 118140960795 + 7303597 * 2 ^ 59
def prefixEnd_7303597 : Nat := 4983230072969 + 3 ^ 40 * 7303597 * 2
def baseEnd_7303597 : Nat := 3750255767735766376848875

theorem tailTrace_7303597 : CollatzResearch.WordTrace tailWord_7303597 prefixEnd_7303597 3750255767735766376848875 := by
  unfold tailWord_7303597
  simp only [CollatzResearch.WordTrace]
  refine ⟨266384066921322898905701045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177589377947548599270467363 266384066921322898905701045)
  ·
    refine ⟨24973506273874021772409473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266384066921322898905701045 24973506273874021772409473)
    ·
      refine ⟨18730129705405516329307105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24973506273874021772409473 18730129705405516329307105)
      ·
        refine ⟨14047597279054137246980329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18730129705405516329307105 14047597279054137246980329)
        ·
          refine ⟨10535697959290602935235247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14047597279054137246980329 10535697959290602935235247)
          ·
            refine ⟨15803546938935904402852871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535697959290602935235247 15803546938935904402852871)
            ·
              refine ⟨23705320408403856604279307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803546938935904402852871 23705320408403856604279307)
              ·
                refine ⟨35557980612605784906418961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23705320408403856604279307 35557980612605784906418961)
                ·
                  refine ⟨26668485459454338679814221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35557980612605784906418961 26668485459454338679814221)
                  ·
                    refine ⟨10000682047295377004930333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26668485459454338679814221 10000682047295377004930333)
                    ·
                      refine ⟨3750255767735766376848875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000682047295377004930333 3750255767735766376848875)
                      ·
                        rfl

theorem cell23_7303597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7303597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303597 prefixEnd_7303597 := by exact prefixLift 7303597
  have htrace : WordTrace (prefixWord ++ tailWord_7303597) baseStart_7303597 baseEnd_7303597 := by
    simpa [prefixWord, tailWord_7303597, baseEnd_7303597] using wordTrace_append hprefix tailTrace_7303597
  have hstable : (prefixWord ++ tailWord_7303597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303597).length < 2 ^ (prefixWord ++ tailWord_7303597).sum := by decide
  have hdescent : baseEnd_7303597 < baseStart_7303597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303647 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 1, 4]
def baseStart_7303647 : Nat := 118140960795 + 7303647 * 2 ^ 59
def prefixEnd_7303647 : Nat := 4983230072969 + 3 ^ 40 * 7303647 * 2
def baseEnd_7303647 : Nat := 1250093813922830393741215

theorem tailTrace_7303647 : CollatzResearch.WordTrace tailWord_7303647 prefixEnd_7303647 1250093813922830393741215 := by
  unfold tailWord_7303647
  simp only [CollatzResearch.WordTrace]
  refine ⟨266385890571141757445021195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177590593714094504963347463 266385890571141757445021195)
  ·
    refine ⟨399578835856712636167531793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266385890571141757445021195 399578835856712636167531793)
    ·
      refine ⟨299684126892534477125648845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399578835856712636167531793 299684126892534477125648845)
      ·
        refine ⟨112381547584700428922118317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299684126892534477125648845 112381547584700428922118317)
        ·
          refine ⟨42143080344262660845794369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112381547584700428922118317 42143080344262660845794369)
          ·
            refine ⟨31607310258196995634345777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42143080344262660845794369 31607310258196995634345777)
            ·
              refine ⟨23705482693647746725759333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31607310258196995634345777 23705482693647746725759333)
              ·
                refine ⟨4444778005058952511079875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23705482693647746725759333 4444778005058952511079875)
                ·
                  refine ⟨6667167007588428766619813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444778005058952511079875 6667167007588428766619813)
                  ·
                    refine ⟨1250093813922830393741215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6667167007588428766619813 1250093813922830393741215)
                    ·
                      rfl

theorem cell23_7303647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 4].length) (baseStart_7303647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303647 prefixEnd_7303647 := by exact prefixLift 7303647
  have htrace : WordTrace (prefixWord ++ tailWord_7303647) baseStart_7303647 baseEnd_7303647 := by
    simpa [prefixWord, tailWord_7303647, baseEnd_7303647] using wordTrace_append hprefix tailTrace_7303647
  have hstable : (prefixWord ++ tailWord_7303647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303647).length < 2 ^ (prefixWord ++ tailWord_7303647).sum := by decide
  have hdescent : baseEnd_7303647 < baseStart_7303647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303660 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 6]
def baseStart_7303660 : Nat := 118140960795 + 7303660 * 2 ^ 59
def prefixEnd_7303660 : Nat := 4983230072969 + 3 ^ 40 * 7303660 * 2
def baseEnd_7303660 : Nat := 416698679668555514484565

theorem tailTrace_7303660 : CollatzResearch.WordTrace tailWord_7303660 prefixEnd_7303660 416698679668555514484565 := by
  unfold tailWord_7303660
  simp only [CollatzResearch.WordTrace]
  refine ⟨133193182360047330332622217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177590909813396440443496289 133193182360047330332622217)
  ·
    refine ⟨99894886770035497749466663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133193182360047330332622217 99894886770035497749466663)
    ·
      refine ⟨149842330155053246624199995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99894886770035497749466663 149842330155053246624199995)
      ·
        refine ⟨224763495232579869936299993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149842330155053246624199995 224763495232579869936299993)
        ·
          refine ⟨168572621424434902452224995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224763495232579869936299993 168572621424434902452224995)
          ·
            refine ⟨252858932136652353678337493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168572621424434902452224995 252858932136652353678337493)
            ·
              refine ⟨5926381221952789539336035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252858932136652353678337493 5926381221952789539336035)
              ·
                refine ⟨8889571832929184309004053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926381221952789539336035 8889571832929184309004053)
                ·
                  refine ⟨416698679668555514484565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8889571832929184309004053 416698679668555514484565)
                  ·
                    rfl

theorem cell23_7303660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_7303660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303660 prefixEnd_7303660 := by exact prefixLift 7303660
  have htrace : WordTrace (prefixWord ++ tailWord_7303660) baseStart_7303660 baseEnd_7303660 := by
    simpa [prefixWord, tailWord_7303660, baseEnd_7303660] using wordTrace_append hprefix tailTrace_7303660
  have hstable : (prefixWord ++ tailWord_7303660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303660).length < 2 ^ (prefixWord ++ tailWord_7303660).sum := by decide
  have hdescent : baseEnd_7303660 < baseStart_7303660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303670 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7303670 : Nat := 118140960795 + 7303670 * 2 ^ 59
def prefixEnd_7303670 : Nat := 4983230072969 + 3 ^ 40 * 7303670 * 2
def baseEnd_7303670 : Nat := 3750293251823544591236039

theorem tailTrace_7303670 : CollatzResearch.WordTrace tailWord_7303670 prefixEnd_7303670 3750293251823544591236039 := by
  unfold tailWord_7303670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16649170590628652023319279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177591152966705621582072309 16649170590628652023319279)
  ·
    refine ⟨24973755885942978034978919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16649170590628652023319279 24973755885942978034978919)
    ·
      refine ⟨37460633828914467052468379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24973755885942978034978919 37460633828914467052468379)
      ·
        refine ⟨56190950743371700578702569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37460633828914467052468379 56190950743371700578702569)
        ·
          refine ⟨42143213057528775434026927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56190950743371700578702569 42143213057528775434026927)
          ·
            refine ⟨63214819586293163151040391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42143213057528775434026927 63214819586293163151040391)
            ·
              refine ⟨94822229379439744726560587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63214819586293163151040391 94822229379439744726560587)
              ·
                refine ⟨142233344069159617089840881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94822229379439744726560587 142233344069159617089840881)
                ·
                  refine ⟨106675008051869712817380661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142233344069159617089840881 106675008051869712817380661)
                  ·
                    refine ⟨10000782004862785576629437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106675008051869712817380661 10000782004862785576629437)
                    ·
                      refine ⟨3750293251823544591236039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000782004862785576629437 3750293251823544591236039)
                      ·
                        rfl

theorem cell23_7303670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7303670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303670 prefixEnd_7303670 := by exact prefixLift 7303670
  have htrace : WordTrace (prefixWord ++ tailWord_7303670) baseStart_7303670 baseEnd_7303670 := by
    simpa [prefixWord, tailWord_7303670, baseEnd_7303670] using wordTrace_append hprefix tailTrace_7303670
  have hstable : (prefixWord ++ tailWord_7303670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303670).length < 2 ^ (prefixWord ++ tailWord_7303670).sum := by decide
  have hdescent : baseEnd_7303670 < baseStart_7303670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303673 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_7303673 : Nat := 118140960795 + 7303673 * 2 ^ 59
def prefixEnd_7303673 : Nat := 4983230072969 + 3 ^ 40 * 7303673 * 2
def baseEnd_7303673 : Nat := 1250098264088502693166175

theorem tailTrace_7303673 : CollatzResearch.WordTrace tailWord_7303673 prefixEnd_7303673 1250098264088502693166175 := by
  unfold tailWord_7303673
  simp only [CollatzResearch.WordTrace]
  refine ⟨266386838869047563885467673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177591225912698375923645115 266386838869047563885467673)
  ·
    refine ⟨199790129151785672914100755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266386838869047563885467673 199790129151785672914100755)
    ·
      refine ⟨299685193727678509371151133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199790129151785672914100755 299685193727678509371151133)
      ·
        refine ⟨112381947647879441014181675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299685193727678509371151133 112381947647879441014181675)
        ·
          refine ⟨168572921471819161521272513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112381947647879441014181675 168572921471819161521272513)
          ·
            refine ⟨126429691103864371140954385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168572921471819161521272513 126429691103864371140954385)
            ·
              refine ⟨94822268327898278355715789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126429691103864371140954385 94822268327898278355715789)
              ·
                refine ⟨35558350622961854383393421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94822268327898278355715789 35558350622961854383393421)
                ·
                  refine ⟨13334381483610695393772533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35558350622961854383393421 13334381483610695393772533)
                  ·
                    refine ⟨1250098264088502693166175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13334381483610695393772533 1250098264088502693166175)
                    ·
                      rfl

theorem cell23_7303673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_7303673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303673 prefixEnd_7303673 := by exact prefixLift 7303673
  have htrace : WordTrace (prefixWord ++ tailWord_7303673) baseStart_7303673 baseEnd_7303673 := by
    simpa [prefixWord, tailWord_7303673, baseEnd_7303673] using wordTrace_append hprefix tailTrace_7303673
  have hstable : (prefixWord ++ tailWord_7303673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303673).length < 2 ^ (prefixWord ++ tailWord_7303673).sum := by decide
  have hdescent : baseEnd_7303673 < baseStart_7303673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303680 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2]
def baseStart_7303680 : Nat := 118140960795 + 7303680 * 2 ^ 59
def prefixEnd_7303680 : Nat := 4983230072969 + 3 ^ 40 * 7303680 * 2
def baseEnd_7303680 : Nat := 3750298386630089552110993

theorem tailTrace_7303680 : CollatzResearch.WordTrace tailWord_7303680 prefixEnd_7303680 3750298386630089552110993 := by
  unfold tailWord_7303680
  simp only [CollatzResearch.WordTrace]
  refine ⟨133193547090011102040486247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177591396120014802720648329 133193547090011102040486247)
  ·
    refine ⟨199790320635016653060729371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133193547090011102040486247 199790320635016653060729371)
    ·
      refine ⟨299685480952524979591094057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199790320635016653060729371 299685480952524979591094057)
      ·
        refine ⟨224764110714393734693320543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299685480952524979591094057 224764110714393734693320543)
        ·
          refine ⟨337146166071590602039980815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224764110714393734693320543 337146166071590602039980815)
          ·
            refine ⟨505719249107385903059971223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337146166071590602039980815 505719249107385903059971223)
            ·
              refine ⟨758578873661078854589956835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505719249107385903059971223 758578873661078854589956835)
              ·
                refine ⟨1137868310491618281884935253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758578873661078854589956835 1137868310491618281884935253)
                ·
                  refine ⟨13334394263573651740839085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1137868310491618281884935253 13334394263573651740839085)
                  ·
                    refine ⟨5000397848840119402814657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13334394263573651740839085 5000397848840119402814657)
                    ·
                      refine ⟨3750298386630089552110993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000397848840119402814657 3750298386630089552110993)
                      ·
                        rfl

theorem cell23_7303680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_7303680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303680 prefixEnd_7303680 := by exact prefixLift 7303680
  have htrace : WordTrace (prefixWord ++ tailWord_7303680) baseStart_7303680 baseEnd_7303680 := by
    simpa [prefixWord, tailWord_7303680, baseEnd_7303680] using wordTrace_append hprefix tailTrace_7303680
  have hstable : (prefixWord ++ tailWord_7303680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303680).length < 2 ^ (prefixWord ++ tailWord_7303680).sum := by decide
  have hdescent : baseEnd_7303680 < baseStart_7303680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303690 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_7303690 : Nat := 118140960795 + 7303690 * 2 ^ 59
def prefixEnd_7303690 : Nat := 4983230072969 + 3 ^ 40 * 7303690 * 2
def baseEnd_7303690 : Nat := 1250101173812211504328649

theorem tailTrace_7303690 : CollatzResearch.WordTrace tailWord_7303690 prefixEnd_7303690 1250101173812211504328649 := by
  unfold tailWord_7303690
  simp only [CollatzResearch.WordTrace]
  refine ⟨66596864727496493947209131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177591639273323983859224349 66596864727496493947209131)
  ·
    refine ⟨99895297091244740920813697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66596864727496493947209131 99895297091244740920813697)
    ·
      refine ⟨74921472818433555690610273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99895297091244740920813697 74921472818433555690610273)
      ·
        refine ⟨56191104613825166767957705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74921472818433555690610273 56191104613825166767957705)
        ·
          refine ⟨42143328460368875075968279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56191104613825166767957705 42143328460368875075968279)
          ·
            refine ⟨63214992690553312613952419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42143328460368875075968279 63214992690553312613952419)
            ·
              refine ⟨94822489035829968920928629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63214992690553312613952419 94822489035829968920928629)
              ·
                refine ⟨8889608347109059586337059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94822489035829968920928629 8889608347109059586337059)
                ·
                  refine ⟨13334412520663589379505589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889608347109059586337059 13334412520663589379505589)
                  ·
                    refine ⟨1250101173812211504328649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13334412520663589379505589 1250101173812211504328649)
                    ·
                      rfl

theorem cell23_7303690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_7303690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303690 prefixEnd_7303690 := by exact prefixLift 7303690
  have htrace : WordTrace (prefixWord ++ tailWord_7303690) baseStart_7303690 baseEnd_7303690 := by
    simpa [prefixWord, tailWord_7303690, baseEnd_7303690] using wordTrace_append hprefix tailTrace_7303690
  have hstable : (prefixWord ++ tailWord_7303690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303690).length < 2 ^ (prefixWord ++ tailWord_7303690).sum := by decide
  have hdescent : baseEnd_7303690 < baseStart_7303690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303704 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7303704 : Nat := 118140960795 + 7303704 * 2 ^ 59
def prefixEnd_7303704 : Nat := 4983230072969 + 3 ^ 40 * 7303704 * 2
def baseEnd_7303704 : Nat := 3750310710165797458210883

theorem tailTrace_7303704 : CollatzResearch.WordTrace tailWord_7303704 prefixEnd_7303704 3750310710165797458210883 := by
  unfold tailWord_7303704
  simp only [CollatzResearch.WordTrace]
  refine ⟨133193984765967628089923083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177591979687956837453230777 133193984765967628089923083)
  ·
    refine ⟨199790977148951442134884625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133193984765967628089923083 199790977148951442134884625)
    ·
      refine ⟨149843232861713581601163469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199790977148951442134884625 149843232861713581601163469)
      ·
        refine ⟨56191212323142593100436301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149843232861713581601163469 56191212323142593100436301)
        ·
          refine ⟨21071704621178472412663613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56191212323142593100436301 21071704621178472412663613)
          ·
            refine ⟨7901889232941927154748855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21071704621178472412663613 7901889232941927154748855)
            ·
              refine ⟨11852833849412890732123283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901889232941927154748855 11852833849412890732123283)
              ·
                refine ⟨17779250774119336098184925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11852833849412890732123283 17779250774119336098184925)
                ·
                  refine ⟨6667219040294751036819347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17779250774119336098184925 6667219040294751036819347)
                  ·
                    refine ⟨10000828560442126555229021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6667219040294751036819347 10000828560442126555229021)
                    ·
                      refine ⟨3750310710165797458210883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000828560442126555229021 3750310710165797458210883)
                      ·
                        rfl

theorem cell23_7303704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7303704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303704 prefixEnd_7303704 := by exact prefixLift 7303704
  have htrace : WordTrace (prefixWord ++ tailWord_7303704) baseStart_7303704 baseEnd_7303704 := by
    simpa [prefixWord, tailWord_7303704, baseEnd_7303704] using wordTrace_append hprefix tailTrace_7303704
  have hstable : (prefixWord ++ tailWord_7303704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303704).length < 2 ^ (prefixWord ++ tailWord_7303704).sum := by decide
  have hdescent : baseEnd_7303704 < baseStart_7303704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303723 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_7303723 : Nat := 118140960795 + 7303723 * 2 ^ 59
def prefixEnd_7303723 : Nat := 4983230072969 + 3 ^ 40 * 7303723 * 2
def baseEnd_7303723 : Nat := 3750320466298232883873295

theorem tailTrace_7303723 : CollatzResearch.WordTrace tailWord_7303723 prefixEnd_7303723 3750320466298232883873295 := by
  unfold tailWord_7303723
  simp only [CollatzResearch.WordTrace]
  refine ⟨266388662518866422424787823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177592441679244281616525215 266388662518866422424787823)
  ·
    refine ⟨399582993778299633637181735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266388662518866422424787823 399582993778299633637181735)
    ·
      refine ⟨599374490667449450455772603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399582993778299633637181735 599374490667449450455772603)
      ·
        refine ⟨899061736001174175683658905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599374490667449450455772603 899061736001174175683658905)
        ·
          refine ⟨674296302000880631762744179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899061736001174175683658905 674296302000880631762744179)
          ·
            refine ⟨1011444453001320947644116269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674296302000880631762744179 1011444453001320947644116269)
            ·
              refine ⟨379291669875495355366543601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1011444453001320947644116269 379291669875495355366543601)
              ·
                refine ⟨284468752406621516524907701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379291669875495355366543601 284468752406621516524907701)
                ·
                  refine ⟨26668945538120767174210097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284468752406621516524907701 26668945538120767174210097)
                  ·
                    refine ⟨20001709153590575380657573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26668945538120767174210097 20001709153590575380657573)
                    ·
                      refine ⟨3750320466298232883873295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20001709153590575380657573 3750320466298232883873295)
                      ·
                        rfl

theorem cell23_7303723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_7303723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303723 prefixEnd_7303723 := by exact prefixLift 7303723
  have htrace : WordTrace (prefixWord ++ tailWord_7303723) baseStart_7303723 baseEnd_7303723 := by
    simpa [prefixWord, tailWord_7303723, baseEnd_7303723] using wordTrace_append hprefix tailTrace_7303723
  have hstable : (prefixWord ++ tailWord_7303723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303723).length < 2 ^ (prefixWord ++ tailWord_7303723).sum := by decide
  have hdescent : baseEnd_7303723 < baseStart_7303723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303733 : List Nat := [1, 3, 3, 1, 1, 2, 1, 11]
def baseStart_7303733 : Nat := 118140960795 + 7303733 * 2 ^ 59
def prefixEnd_7303733 : Nat := 4983230072969 + 3 ^ 40 * 7303733 * 2
def baseEnd_7303733 : Nat := 138900948189065846101787

theorem tailTrace_7303733 : CollatzResearch.WordTrace tailWord_7303733 prefixEnd_7303733 138900948189065846101787 := by
  unfold tailWord_7303733
  simp only [CollatzResearch.WordTrace]
  refine ⟨266389027248830194132651853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177592684832553462755101235 266389027248830194132651853)
  ·
    refine ⟨99895885218311322799744445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266389027248830194132651853 99895885218311322799744445)
    ·
      refine ⟨37460956956866746049904167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99895885218311322799744445 37460956956866746049904167)
      ·
        refine ⟨56191435435300119074856251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37460956956866746049904167 56191435435300119074856251)
        ·
          refine ⟨84287153152950178612284377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56191435435300119074856251 84287153152950178612284377)
          ·
            refine ⟨63215364864712633959213283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84287153152950178612284377 63215364864712633959213283)
            ·
              refine ⟨94823047297068950938819925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63215364864712633959213283 94823047297068950938819925)
              ·
                refine ⟨138900948189065846101787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94823047297068950938819925 138900948189065846101787)
                ·
                  rfl

theorem cell23_7303733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 11].length) (baseStart_7303733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303733 prefixEnd_7303733 := by exact prefixLift 7303733
  have htrace : WordTrace (prefixWord ++ tailWord_7303733) baseStart_7303733 baseEnd_7303733 := by
    simpa [prefixWord, tailWord_7303733, baseEnd_7303733] using wordTrace_append hprefix tailTrace_7303733
  have hstable : (prefixWord ++ tailWord_7303733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303733).length < 2 ^ (prefixWord ++ tailWord_7303733).sum := by decide
  have hdescent : baseEnd_7303733 < baseStart_7303733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303740 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7303740 : Nat := 118140960795 + 7303740 * 2 ^ 59
def prefixEnd_7303740 : Nat := 4983230072969 + 3 ^ 40 * 7303740 * 2
def baseEnd_7303740 : Nat := 3750329195469359317360717

theorem tailTrace_7303740 : CollatzResearch.WordTrace tailWord_7303740 prefixEnd_7303740 3750329195469359317360717 := by
  unfold tailWord_7303740
  simp only [CollatzResearch.WordTrace]
  refine ⟨133194641279902417164078337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177592855039869889552104449 133194641279902417164078337)
  ·
    refine ⟨99895980959926812873058753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133194641279902417164078337 99895980959926812873058753)
    ·
      refine ⟨74921985719945109654794065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99895980959926812873058753 74921985719945109654794065)
      ·
        refine ⟨56191489289958832241095549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74921985719945109654794065 56191489289958832241095549)
        ·
          refine ⟨21071808483734562090410831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56191489289958832241095549 21071808483734562090410831)
          ·
            refine ⟨31607712725601843135616247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21071808483734562090410831 31607712725601843135616247)
            ·
              refine ⟨47411569088402764703424371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31607712725601843135616247 47411569088402764703424371)
              ·
                refine ⟨71117353632604147055136557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47411569088402764703424371 71117353632604147055136557)
                ·
                  refine ⟨26669007612226555145676209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71117353632604147055136557 26669007612226555145676209)
                  ·
                    refine ⟨20001755709169916359257157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26669007612226555145676209 20001755709169916359257157)
                    ·
                      refine ⟨3750329195469359317360717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20001755709169916359257157 3750329195469359317360717)
                      ·
                        rfl

theorem cell23_7303740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7303740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303740 prefixEnd_7303740 := by exact prefixLift 7303740
  have htrace : WordTrace (prefixWord ++ tailWord_7303740) baseStart_7303740 baseEnd_7303740 := by
    simpa [prefixWord, tailWord_7303740, baseEnd_7303740] using wordTrace_append hprefix tailTrace_7303740
  have hstable : (prefixWord ++ tailWord_7303740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303740).length < 2 ^ (prefixWord ++ tailWord_7303740).sum := by decide
  have hdescent : baseEnd_7303740 < baseStart_7303740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303761 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 1, 2, 2]
def baseStart_7303761 : Nat := 118140960795 + 7303761 * 2 ^ 59
def prefixEnd_7303761 : Nat := 4983230072969 + 3 ^ 40 * 7303761 * 2
def baseEnd_7303761 : Nat := 3750339978563103735198121

theorem tailTrace_7303761 : CollatzResearch.WordTrace tailWord_7303761 prefixEnd_7303761 3750339978563103735198121 := by
  unfold tailWord_7303761
  simp only [CollatzResearch.WordTrace]
  refine ⟨266390048492728754914671137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177593365661819169943114091 266390048492728754914671137)
  ·
    refine ⟨199792536369546566186003353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266390048492728754914671137 199792536369546566186003353)
    ·
      refine ⟨149844402277159924639502515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199792536369546566186003353 149844402277159924639502515)
      ·
        refine ⟨224766603415739886959253773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149844402277159924639502515 224766603415739886959253773)
        ·
          refine ⟨84287476280902457609720165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224766603415739886959253773 84287476280902457609720165)
          ·
            refine ⟨15803901802669210801822531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84287476280902457609720165 15803901802669210801822531)
            ·
              refine ⟨23705852704003816202733797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803901802669210801822531 23705852704003816202733797)
              ·
                refine ⟨4444847382000715538012587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23705852704003816202733797 4444847382000715538012587)
                ·
                  refine ⟨6667271073001073307018881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444847382000715538012587 6667271073001073307018881)
                  ·
                    refine ⟨5000453304750804980264161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667271073001073307018881 5000453304750804980264161)
                    ·
                      refine ⟨3750339978563103735198121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000453304750804980264161 3750339978563103735198121)
                      ·
                        rfl

theorem cell23_7303761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_7303761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303761 prefixEnd_7303761 := by exact prefixLift 7303761
  have htrace : WordTrace (prefixWord ++ tailWord_7303761) baseStart_7303761 baseEnd_7303761 := by
    simpa [prefixWord, tailWord_7303761, baseEnd_7303761] using wordTrace_append hprefix tailTrace_7303761
  have hstable : (prefixWord ++ tailWord_7303761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303761).length < 2 ^ (prefixWord ++ tailWord_7303761).sum := by decide
  have hdescent : baseEnd_7303761 < baseStart_7303761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303777 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_7303777 : Nat := 118140960795 + 7303777 * 2 ^ 59
def prefixEnd_7303777 : Nat := 4983230072969 + 3 ^ 40 * 7303777 * 2
def baseEnd_7303777 : Nat := 3750348194253575672598047

theorem tailTrace_7303777 : CollatzResearch.WordTrace tailWord_7303777 prefixEnd_7303777 3750348194253575672598047 := by
  unfold tailWord_7303777
  simp only [CollatzResearch.WordTrace]
  refine ⟨266390632060670789647253585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177593754707113859764835723 266390632060670789647253585)
  ·
    refine ⟨199792974045503092235440189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266390632060670789647253585 199792974045503092235440189)
    ·
      refine ⟨74922365267063659588290071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199792974045503092235440189 74922365267063659588290071)
      ·
        refine ⟨112383547900595489382435107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74922365267063659588290071 112383547900595489382435107)
        ·
          refine ⟨168575321850893234073652661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112383547900595489382435107 168575321850893234073652661)
          ·
            refine ⟨15803936423521240694404937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168575321850893234073652661 15803936423521240694404937)
            ·
              refine ⟨11852952317640930520803703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15803936423521240694404937 11852952317640930520803703)
              ·
                refine ⟨17779428476461395781205555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11852952317640930520803703 17779428476461395781205555)
                ·
                  refine ⟨26669142714692093671808333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17779428476461395781205555 26669142714692093671808333)
                  ·
                    refine ⟨10000928518009535126928125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26669142714692093671808333 10000928518009535126928125)
                    ·
                      refine ⟨3750348194253575672598047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000928518009535126928125 3750348194253575672598047)
                      ·
                        rfl

theorem cell23_7303777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_7303777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303777 prefixEnd_7303777 := by exact prefixLift 7303777
  have htrace : WordTrace (prefixWord ++ tailWord_7303777) baseStart_7303777 baseEnd_7303777 := by
    simpa [prefixWord, tailWord_7303777, baseEnd_7303777] using wordTrace_append hprefix tailTrace_7303777
  have hstable : (prefixWord ++ tailWord_7303777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303777).length < 2 ^ (prefixWord ++ tailWord_7303777).sum := by decide
  have hdescent : baseEnd_7303777 < baseStart_7303777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303778 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7303778 : Nat := 118140960795 + 7303778 * 2 ^ 59
def prefixEnd_7303778 : Nat := 4983230072969 + 3 ^ 40 * 7303778 * 2
def baseEnd_7303778 : Nat := 3750348707734230168685543

theorem tailTrace_7303778 : CollatzResearch.WordTrace tailWord_7303778 prefixEnd_7303778 3750348707734230168685543 := by
  unfold tailWord_7303778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66597667133416791704509997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177593779022444777878693325 66597667133416791704509997)
  ·
    refine ⟨24974125175031296889191249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66597667133416791704509997 24974125175031296889191249)
    ·
      refine ⟨18730593881273472666893437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24974125175031296889191249 18730593881273472666893437)
      ·
        refine ⟨7023972705477552250085039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18730593881273472666893437 7023972705477552250085039)
        ·
          refine ⟨10535959058216328375127559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023972705477552250085039 10535959058216328375127559)
          ·
            refine ⟨15803938587324492562691339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535959058216328375127559 15803938587324492562691339)
            ·
              refine ⟨23705907880986738844037009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803938587324492562691339 23705907880986738844037009)
              ·
                refine ⟨17779430910740054133027757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23705907880986738844037009 17779430910740054133027757)
                ·
                  refine ⟨6667286591527520299885409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17779430910740054133027757 6667286591527520299885409)
                  ·
                    refine ⟨5000464943645640224914057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667286591527520299885409 5000464943645640224914057)
                    ·
                      refine ⟨3750348707734230168685543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000464943645640224914057 3750348707734230168685543)
                      ·
                        rfl

theorem cell23_7303778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7303778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303778 prefixEnd_7303778 := by exact prefixLift 7303778
  have htrace : WordTrace (prefixWord ++ tailWord_7303778) baseStart_7303778 baseEnd_7303778 := by
    simpa [prefixWord, tailWord_7303778, baseEnd_7303778] using wordTrace_append hprefix tailTrace_7303778
  have hstable : (prefixWord ++ tailWord_7303778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303778).length < 2 ^ (prefixWord ++ tailWord_7303778).sum := by decide
  have hdescent : baseEnd_7303778 < baseStart_7303778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303798 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7303798 : Nat := 118140960795 + 7303798 * 2 ^ 59
def prefixEnd_7303798 : Nat := 4983230072969 + 3 ^ 40 * 7303798 * 2
def baseEnd_7303798 : Nat := 3750358977347320090435451

theorem tailTrace_7303798 : CollatzResearch.WordTrace tailWord_7303798 prefixEnd_7303798 3750358977347320090435451 := by
  unfold tailWord_7303798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16649462374599669389610503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177594265329063140155845365 16649462374599669389610503)
  ·
    refine ⟨24974193561899504084415755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16649462374599669389610503 24974193561899504084415755)
    ·
      refine ⟨37461290342849256126623633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24974193561899504084415755 37461290342849256126623633)
      ·
        refine ⟨28095967757136942094967725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37461290342849256126623633 28095967757136942094967725)
        ·
          refine ⟨10535987908926353285612897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28095967757136942094967725 10535987908926353285612897)
          ·
            refine ⟨7901990931694764964209673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10535987908926353285612897 7901990931694764964209673)
            ·
              refine ⟨5926493198771073723157255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901990931694764964209673 5926493198771073723157255)
              ·
                refine ⟨8889739798156610584735883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926493198771073723157255 8889739798156610584735883)
                ·
                  refine ⟨13334609697234915877103825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889739798156610584735883 13334609697234915877103825)
                  ·
                    refine ⟨10000957272926186907827869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13334609697234915877103825 10000957272926186907827869)
                    ·
                      refine ⟨3750358977347320090435451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000957272926186907827869 3750358977347320090435451)
                      ·
                        rfl

theorem cell23_7303798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7303798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303798 prefixEnd_7303798 := by exact prefixLift 7303798
  have htrace : WordTrace (prefixWord ++ tailWord_7303798) baseStart_7303798 baseEnd_7303798 := by
    simpa [prefixWord, tailWord_7303798, baseEnd_7303798] using wordTrace_append hprefix tailTrace_7303798
  have hstable : (prefixWord ++ tailWord_7303798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303798).length < 2 ^ (prefixWord ++ tailWord_7303798).sum := by decide
  have hdescent : baseEnd_7303798 < baseStart_7303798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303820 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_7303820 : Nat := 118140960795 + 7303820 * 2 ^ 59
def prefixEnd_7303820 : Nat := 4983230072969 + 3 ^ 40 * 7303820 * 2
def baseEnd_7303820 : Nat := 3750370273921719004360349

theorem tailTrace_7303820 : CollatzResearch.WordTrace tailWord_7303820 prefixEnd_7303820 3750370273921719004360349 := by
  unfold tailWord_7303820
  simp only [CollatzResearch.WordTrace]
  refine ⟨133196100199757503995534457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177594800266343338660712609 133196100199757503995534457)
  ·
    refine ⟨99897075149818127996650843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133196100199757503995534457 99897075149818127996650843)
    ·
      refine ⟨149845612724727191994976265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99897075149818127996650843 149845612724727191994976265)
      ·
        refine ⟨112384209543545393996232199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149845612724727191994976265 112384209543545393996232199)
        ·
          refine ⟨168576314315318090994348299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112384209543545393996232199 168576314315318090994348299)
          ·
            refine ⟨252864471472977136491522449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168576314315318090994348299 252864471472977136491522449)
            ·
              refine ⟨189648353604732852368641837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252864471472977136491522449 189648353604732852368641837)
              ·
                refine ⟨71118132601774819638240689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189648353604732852368641837 71118132601774819638240689)
                ·
                  refine ⟨53338599451331114728680517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71118132601774819638240689 53338599451331114728680517)
                  ·
                    refine ⟨10000987397124584011627597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53338599451331114728680517 10000987397124584011627597)
                    ·
                      refine ⟨3750370273921719004360349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000987397124584011627597 3750370273921719004360349)
                      ·
                        rfl

theorem cell23_7303820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_7303820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303820 prefixEnd_7303820 := by exact prefixLift 7303820
  have htrace : WordTrace (prefixWord ++ tailWord_7303820) baseStart_7303820 baseEnd_7303820 := by
    simpa [prefixWord, tailWord_7303820, baseEnd_7303820] using wordTrace_append hprefix tailTrace_7303820
  have hstable : (prefixWord ++ tailWord_7303820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303820).length < 2 ^ (prefixWord ++ tailWord_7303820).sum := by decide
  have hdescent : baseEnd_7303820 < baseStart_7303820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303823 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 11]
def baseStart_7303823 : Nat := 118140960795 + 7303823 * 2 ^ 59
def prefixEnd_7303823 : Nat := 4983230072969 + 3 ^ 40 * 7303823 * 2
def baseEnd_7303823 : Nat := 416707979373742499180315

theorem tailTrace_7303823 : CollatzResearch.WordTrace tailWord_7303823 prefixEnd_7303823 416707979373742499180315 := by
  unfold tailWord_7303823
  simp only [CollatzResearch.WordTrace]
  refine ⟨266392309818504139503428123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177594873212336093002285415 266392309818504139503428123)
  ·
    refine ⟨399588464727756209255142185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266392309818504139503428123 399588464727756209255142185)
    ·
      refine ⟨299691348545817156941356639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399588464727756209255142185 299691348545817156941356639)
      ·
        refine ⟨449537022818725735412034959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299691348545817156941356639 449537022818725735412034959)
        ·
          refine ⟨674305534228088603118052439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449537022818725735412034959 674305534228088603118052439)
          ·
            refine ⟨1011458301342132904677078659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674305534228088603118052439 1011458301342132904677078659)
            ·
              refine ⟨1517187452013199357015617989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011458301342132904677078659 1517187452013199357015617989)
              ·
                refine ⟨284472647252474879440428373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1517187452013199357015617989 284472647252474879440428373)
                ·
                  refine ⟨416707979373742499180315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 284472647252474879440428373 416707979373742499180315)
                  ·
                    rfl

theorem cell23_7303823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 11].length) (baseStart_7303823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303823 prefixEnd_7303823 := by exact prefixLift 7303823
  have htrace : WordTrace (prefixWord ++ tailWord_7303823) baseStart_7303823 baseEnd_7303823 := by
    simpa [prefixWord, tailWord_7303823, baseEnd_7303823] using wordTrace_append hprefix tailTrace_7303823
  have hstable : (prefixWord ++ tailWord_7303823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303823).length < 2 ^ (prefixWord ++ tailWord_7303823).sum := by decide
  have hdescent : baseEnd_7303823 < baseStart_7303823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303828 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7303828 : Nat := 118140960795 + 7303828 * 2 ^ 59
def prefixEnd_7303828 : Nat := 4983230072969 + 3 ^ 40 * 7303828 * 2
def baseEnd_7303828 : Nat := 3750374381766954973060313

theorem tailTrace_7303828 : CollatzResearch.WordTrace tailWord_7303828 prefixEnd_7303828 3750374381766954973060313 := by
  unfold tailWord_7303828
  simp only [CollatzResearch.WordTrace]
  refine ⟨133196246091743012678680069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177594994788990683571573425 133196246091743012678680069)
  ·
    refine ⟨24974296142201814877252513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133196246091743012678680069 24974296142201814877252513)
    ·
      refine ⟨18730722106651361157939385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24974296142201814877252513 18730722106651361157939385)
      ·
        refine ⟨14048041579988520868454539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18730722106651361157939385 14048041579988520868454539)
        ·
          refine ⟨21072062369982781302681809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048041579988520868454539 21072062369982781302681809)
          ·
            refine ⟨15804046777487085977011357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21072062369982781302681809 15804046777487085977011357)
            ·
              refine ⟨5926517541557657241379259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15804046777487085977011357 5926517541557657241379259)
              ·
                refine ⟨8889776312336485862068889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926517541557657241379259 8889776312336485862068889)
                ·
                  refine ⟨6667332234252364396551667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8889776312336485862068889 6667332234252364396551667)
                  ·
                    refine ⟨10000998351378546594827501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6667332234252364396551667 10000998351378546594827501)
                    ·
                      refine ⟨3750374381766954973060313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10000998351378546594827501 3750374381766954973060313)
                      ·
                        rfl

theorem cell23_7303828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7303828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303828 prefixEnd_7303828 := by exact prefixLift 7303828
  have htrace : WordTrace (prefixWord ++ tailWord_7303828) baseStart_7303828 baseEnd_7303828 := by
    simpa [prefixWord, tailWord_7303828, baseEnd_7303828] using wordTrace_append hprefix tailTrace_7303828
  have hstable : (prefixWord ++ tailWord_7303828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303828).length < 2 ^ (prefixWord ++ tailWord_7303828).sum := by decide
  have hdescent : baseEnd_7303828 < baseStart_7303828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303854 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7303854 : Nat := 118140960795 + 7303854 * 2 ^ 59
def prefixEnd_7303854 : Nat := 4983230072969 + 3 ^ 40 * 7303854 * 2
def baseEnd_7303854 : Nat := 3750387732263971871335193

theorem tailTrace_7303854 : CollatzResearch.WordTrace tailWord_7303854 prefixEnd_7303854 3750387732263971871335193 := by
  unfold tailWord_7303854
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299180060173978974725827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177595626987594554531871077 33299180060173978974725827)
  ·
    refine ⟨49948770090260968462088741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33299180060173978974725827 49948770090260968462088741)
    ·
      refine ⟨9365394391923931586641639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49948770090260968462088741 9365394391923931586641639)
      ·
        refine ⟨14048091587885897379962459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365394391923931586641639 14048091587885897379962459)
        ·
          refine ⟨21072137381828846069943689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048091587885897379962459 21072137381828846069943689)
          ·
            refine ⟨15804103036371634552457767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21072137381828846069943689 15804103036371634552457767)
            ·
              refine ⟨23706154554557451828686651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15804103036371634552457767 23706154554557451828686651)
              ·
                refine ⟨35559231831836177743029977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23706154554557451828686651 35559231831836177743029977)
                ·
                  refine ⟨26669423873877133307272483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35559231831836177743029977 26669423873877133307272483)
                  ·
                    refine ⟨40004135810815699960908725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26669423873877133307272483 40004135810815699960908725)
                    ·
                      refine ⟨3750387732263971871335193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40004135810815699960908725 3750387732263971871335193)
                      ·
                        rfl

theorem cell23_7303854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7303854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303854 prefixEnd_7303854 := by exact prefixLift 7303854
  have htrace : WordTrace (prefixWord ++ tailWord_7303854) baseStart_7303854 baseEnd_7303854 := by
    simpa [prefixWord, tailWord_7303854, baseEnd_7303854] using wordTrace_append hprefix tailTrace_7303854
  have hstable : (prefixWord ++ tailWord_7303854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303854).length < 2 ^ (prefixWord ++ tailWord_7303854).sum := by decide
  have hdescent : baseEnd_7303854 < baseStart_7303854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303880 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7303880 : Nat := 118140960795 + 7303880 * 2 ^ 59
def prefixEnd_7303880 : Nat := 4983230072969 + 3 ^ 40 * 7303880 * 2
def baseEnd_7303880 : Nat := 3750401082760988769610073

theorem tailTrace_7303880 : CollatzResearch.WordTrace tailWord_7303880 prefixEnd_7303880 3750401082760988769610073 := by
  unfold tailWord_7303880
  simp only [CollatzResearch.WordTrace]
  refine ⟨133197194389648819119126547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177596259186198425492168729 133197194389648819119126547)
  ·
    refine ⟨199795791584473228678689821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133197194389648819119126547 199795791584473228678689821)
    ·
      refine ⟨74923421844177460754508683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199795791584473228678689821 74923421844177460754508683)
      ·
        refine ⟨112385132766266191131763025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74923421844177460754508683 112385132766266191131763025)
        ·
          refine ⟨84288849574699643348822269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112385132766266191131763025 84288849574699643348822269)
          ·
            refine ⟨31608318590512366255808351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84288849574699643348822269 31608318590512366255808351)
            ·
              refine ⟨47412477885768549383712527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31608318590512366255808351 47412477885768549383712527)
              ·
                refine ⟨71118716828652824075568791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47412477885768549383712527 71118716828652824075568791)
                ·
                  refine ⟨106678075242979236113353187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71118716828652824075568791 106678075242979236113353187)
                  ·
                    refine ⟨160017112864468854170029781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106678075242979236113353187 160017112864468854170029781)
                    ·
                      refine ⟨3750401082760988769610073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160017112864468854170029781 3750401082760988769610073)
                      ·
                        rfl

theorem cell23_7303880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7303880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303880 prefixEnd_7303880 := by exact prefixLift 7303880
  have htrace : WordTrace (prefixWord ++ tailWord_7303880) baseStart_7303880 baseEnd_7303880 := by
    simpa [prefixWord, tailWord_7303880, baseEnd_7303880] using wordTrace_append hprefix tailTrace_7303880
  have hstable : (prefixWord ++ tailWord_7303880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303880).length < 2 ^ (prefixWord ++ tailWord_7303880).sum := by decide
  have hdescent : baseEnd_7303880 < baseStart_7303880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303885 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7303885 : Nat := 118140960795 + 7303885 * 2 ^ 59
def prefixEnd_7303885 : Nat := 4983230072969 + 3 ^ 40 * 7303885 * 2
def baseEnd_7303885 : Nat := 3750403650164261250047551

theorem tailTrace_7303885 : CollatzResearch.WordTrace tailWord_7303885 prefixEnd_7303885 3750403650164261250047551 := by
  unfold tailWord_7303885
  simp only [CollatzResearch.WordTrace]
  refine ⟨266394571144279524092185109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177596380762853016061456739 266394571144279524092185109)
  ·
    refine ⟨12487245522388102691821177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266394571144279524092185109 12487245522388102691821177)
    ·
      refine ⟨9365434141791077018865883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12487245522388102691821177 9365434141791077018865883)
      ·
        refine ⟨14048151212686615528298825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365434141791077018865883 14048151212686615528298825)
        ·
          refine ⟨10536113409514961646224119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14048151212686615528298825 10536113409514961646224119)
          ·
            refine ⟨15804170114272442469336179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536113409514961646224119 15804170114272442469336179)
            ·
              refine ⟨23706255171408663704004269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15804170114272442469336179 23706255171408663704004269)
              ·
                refine ⟨8889845689278248889001601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23706255171408663704004269 8889845689278248889001601)
                ·
                  refine ⟨6667384266958686666751201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8889845689278248889001601 6667384266958686666751201)
                  ·
                    refine ⟨5000538200219015000063401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667384266958686666751201 5000538200219015000063401)
                    ·
                      refine ⟨3750403650164261250047551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000538200219015000063401 3750403650164261250047551)
                      ·
                        rfl

theorem cell23_7303885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7303885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303885 prefixEnd_7303885 := by exact prefixLift 7303885
  have htrace : WordTrace (prefixWord ++ tailWord_7303885) baseStart_7303885 baseEnd_7303885 := by
    simpa [prefixWord, tailWord_7303885, baseEnd_7303885] using wordTrace_append hprefix tailTrace_7303885
  have hstable : (prefixWord ++ tailWord_7303885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303885).length < 2 ^ (prefixWord ++ tailWord_7303885).sum := by decide
  have hdescent : baseEnd_7303885 < baseStart_7303885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303920 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_7303920 : Nat := 118140960795 + 7303920 * 2 ^ 59
def prefixEnd_7303920 : Nat := 4983230072969 + 3 ^ 40 * 7303920 * 2
def baseEnd_7303920 : Nat := 3750421621987168613109889

theorem tailTrace_7303920 : CollatzResearch.WordTrace tailWord_7303920 prefixEnd_7303920 3750421621987168613109889 := by
  unfold tailWord_7303920
  simp only [CollatzResearch.WordTrace]
  refine ⟨133197923849576362534854607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177597231799435150046472809 133197923849576362534854607)
  ·
    refine ⟨199796885774364543802281911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133197923849576362534854607 199796885774364543802281911)
    ·
      refine ⟨299695328661546815703422867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199796885774364543802281911 299695328661546815703422867)
      ·
        refine ⟨449542992992320223555134301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299695328661546815703422867 449542992992320223555134301)
        ·
          refine ⟨168578622372120083833175363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449542992992320223555134301 168578622372120083833175363)
          ·
            refine ⟨252867933558180125749763045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168578622372120083833175363 252867933558180125749763045)
            ·
              refine ⟨47412737542158773578080571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252867933558180125749763045 47412737542158773578080571)
              ·
                refine ⟨71119106313238160367120857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47412737542158773578080571 71119106313238160367120857)
                ·
                  refine ⟨53339329734928620275340643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71119106313238160367120857 53339329734928620275340643)
                  ·
                    refine ⟨80008994602392930413010965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53339329734928620275340643 80008994602392930413010965)
                    ·
                      refine ⟨3750421621987168613109889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80008994602392930413010965 3750421621987168613109889)
                      ·
                        rfl

theorem cell23_7303920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_7303920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303920 prefixEnd_7303920 := by exact prefixLift 7303920
  have htrace : WordTrace (prefixWord ++ tailWord_7303920) baseStart_7303920 baseEnd_7303920 := by
    simpa [prefixWord, tailWord_7303920, baseEnd_7303920] using wordTrace_append hprefix tailTrace_7303920
  have hstable : (prefixWord ++ tailWord_7303920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303920).length < 2 ^ (prefixWord ++ tailWord_7303920).sum := by decide
  have hdescent : baseEnd_7303920 < baseStart_7303920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303930 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_7303930 : Nat := 118140960795 + 7303930 * 2 ^ 59
def prefixEnd_7303930 : Nat := 4983230072969 + 3 ^ 40 * 7303930 * 2
def baseEnd_7303930 : Nat := 416714084088190397109427

theorem tailTrace_7303930 : CollatzResearch.WordTrace tailWord_7303930 prefixEnd_7303930 416714084088190397109427 := by
  unfold tailWord_7303930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66599053107279124194393311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177597474952744331185048829 66599053107279124194393311)
  ·
    refine ⟨99898579660918686291589967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66599053107279124194393311 99898579660918686291589967)
    ·
      refine ⟨149847869491378029437384951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99898579660918686291589967 149847869491378029437384951)
      ·
        refine ⟨224771804237067044156077427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149847869491378029437384951 224771804237067044156077427)
        ·
          refine ⟨337157706355600566234116141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224771804237067044156077427 337157706355600566234116141)
          ·
            refine ⟨126434139883350212337793553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337157706355600566234116141 126434139883350212337793553)
            ·
              refine ⟨94825604912512659253345165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126434139883350212337793553 94825604912512659253345165)
              ·
                refine ⟨35559601842192247220004437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94825604912512659253345165 35559601842192247220004437)
                ·
                  refine ⟨416714084088190397109427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35559601842192247220004437 416714084088190397109427)
                  ·
                    rfl

theorem cell23_7303930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_7303930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303930 prefixEnd_7303930 := by exact prefixLift 7303930
  have htrace : WordTrace (prefixWord ++ tailWord_7303930) baseStart_7303930 baseEnd_7303930 := by
    simpa [prefixWord, tailWord_7303930, baseEnd_7303930] using wordTrace_append hprefix tailTrace_7303930
  have hstable : (prefixWord ++ tailWord_7303930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303930).length < 2 ^ (prefixWord ++ tailWord_7303930).sum := by decide
  have hdescent : baseEnd_7303930 < baseStart_7303930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303977 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_7303977 : Nat := 118140960795 + 7303977 * 2 ^ 59
def prefixEnd_7303977 : Nat := 4983230072969 + 3 ^ 40 * 7303977 * 2
def baseEnd_7303977 : Nat := 1250150296794824963365709

theorem tailTrace_7303977 : CollatzResearch.WordTrace tailWord_7303977 prefixEnd_7303977 1250150296794824963365709 := by
  unfold tailWord_7303977
  simp only [CollatzResearch.WordTrace]
  refine ⟨266397926659946223804534185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177598617773297482536356123 266397926659946223804534185)
  ·
    refine ⟨199798444994959667853400639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266397926659946223804534185 199798444994959667853400639)
    ·
      refine ⟨299697667492439501780100959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199798444994959667853400639 299697667492439501780100959)
      ·
        refine ⟨449546501238659252670151439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299697667492439501780100959 449546501238659252670151439)
        ·
          refine ⟨674319751857988879005227159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449546501238659252670151439 674319751857988879005227159)
          ·
            refine ⟨1011479627786983318507840739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674319751857988879005227159 1011479627786983318507840739)
            ·
              refine ⟨1517219441680474977761761109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011479627786983318507840739 1517219441680474977761761109)
              ·
                refine ⟨8889957666096533072822819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1517219441680474977761761109 8889957666096533072822819)
                ·
                  refine ⟨13334936499144799609234229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889957666096533072822819 13334936499144799609234229)
                  ·
                    refine ⟨1250150296794824963365709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13334936499144799609234229 1250150296794824963365709)
                    ·
                      rfl

theorem cell23_7303977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_7303977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303977 prefixEnd_7303977 := by exact prefixLift 7303977
  have htrace : WordTrace (prefixWord ++ tailWord_7303977) baseStart_7303977 baseEnd_7303977 := by
    simpa [prefixWord, tailWord_7303977, baseEnd_7303977] using wordTrace_append hprefix tailTrace_7303977
  have hstable : (prefixWord ++ tailWord_7303977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303977).length < 2 ^ (prefixWord ++ tailWord_7303977).sum := by decide
  have hdescent : baseEnd_7303977 < baseStart_7303977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303981 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7303981 : Nat := 118140960795 + 7303981 * 2 ^ 59
def prefixEnd_7303981 : Nat := 4983230072969 + 3 ^ 40 * 7303981 * 2
def baseEnd_7303981 : Nat := 416716993811899208271901

theorem tailTrace_7303981 : CollatzResearch.WordTrace tailWord_7303981 prefixEnd_7303981 416716993811899208271901 := by
  unfold tailWord_7303981
  simp only [CollatzResearch.WordTrace]
  refine ⟨266398072551931732487679797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177598715034621154991786531 266398072551931732487679797)
  ·
    refine ⟨24974819301743599920719981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266398072551931732487679797 24974819301743599920719981)
    ·
      refine ⟨9365557238153849970269993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24974819301743599920719981 9365557238153849970269993)
      ·
        refine ⟨7024167928615387477702495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9365557238153849970269993 7024167928615387477702495)
        ·
          refine ⟨10536251892923081216553743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024167928615387477702495 10536251892923081216553743)
          ·
            refine ⟨15804377839384621824830615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536251892923081216553743 15804377839384621824830615)
            ·
              refine ⟨23706566759076932737245923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15804377839384621824830615 23706566759076932737245923)
              ·
                refine ⟨35559850138615399105868885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23706566759076932737245923 35559850138615399105868885)
                ·
                  refine ⟨416716993811899208271901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35559850138615399105868885 416716993811899208271901)
                  ·
                    rfl

theorem cell23_7303981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7303981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303981 prefixEnd_7303981 := by exact prefixLift 7303981
  have htrace : WordTrace (prefixWord ++ tailWord_7303981) baseStart_7303981 baseEnd_7303981 := by
    simpa [prefixWord, tailWord_7303981, baseEnd_7303981] using wordTrace_append hprefix tailTrace_7303981
  have hstable : (prefixWord ++ tailWord_7303981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303981).length < 2 ^ (prefixWord ++ tailWord_7303981).sum := by decide
  have hdescent : baseEnd_7303981 < baseStart_7303981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303984 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2]
def baseStart_7303984 : Nat := 118140960795 + 7303984 * 2 ^ 59
def prefixEnd_7303984 : Nat := 4983230072969 + 3 ^ 40 * 7303984 * 2
def baseEnd_7303984 : Nat := 3750454484749056362709595

theorem tailTrace_7303984 : CollatzResearch.WordTrace tailWord_7303984 prefixEnd_7303984 3750454484749056362709595 := by
  unfold tailWord_7303984
  simp only [CollatzResearch.WordTrace]
  refine ⟨133199090985460432000019503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177598787980613909333359337 133199090985460432000019503)
  ·
    refine ⟨199798636478190648000029255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133199090985460432000019503 199798636478190648000029255)
    ·
      refine ⟨299697954717285972000043883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199798636478190648000029255 299697954717285972000043883)
      ·
        refine ⟨449546932075928958000065825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299697954717285972000043883 449546932075928958000065825)
        ·
          refine ⟨337160199056946718500049369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449546932075928958000065825 337160199056946718500049369)
          ·
            refine ⟨252870149292710038875037027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337160199056946718500049369 252870149292710038875037027)
            ·
              refine ⟨379305223939065058312555541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252870149292710038875037027 379305223939065058312555541)
              ·
                refine ⟨17779932372143674608401041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 379305223939065058312555541 17779932372143674608401041)
                ·
                  refine ⟨13334949279107755956300781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17779932372143674608401041 13334949279107755956300781)
                  ·
                    refine ⟨5000605979665408483612793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13334949279107755956300781 5000605979665408483612793)
                    ·
                      refine ⟨3750454484749056362709595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000605979665408483612793 3750454484749056362709595)
                      ·
                        rfl

theorem cell23_7303984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2].length) (baseStart_7303984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303984 prefixEnd_7303984 := by exact prefixLift 7303984
  have htrace : WordTrace (prefixWord ++ tailWord_7303984) baseStart_7303984 baseEnd_7303984 := by
    simpa [prefixWord, tailWord_7303984, baseEnd_7303984] using wordTrace_append hprefix tailTrace_7303984
  have hstable : (prefixWord ++ tailWord_7303984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303984).length < 2 ^ (prefixWord ++ tailWord_7303984).sum := by decide
  have hdescent : baseEnd_7303984 < baseStart_7303984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7303991 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 1, 1, 3]
def baseStart_7303991 : Nat := 118140960795 + 7303991 * 2 ^ 59
def prefixEnd_7303991 : Nat := 4983230072969 + 3 ^ 40 * 7303991 * 2
def baseEnd_7303991 : Nat := 3750458079113637835322063

theorem tailTrace_7303991 : CollatzResearch.WordTrace tailWord_7303991 prefixEnd_7303991 3750458079113637835322063 := by
  unfold tailWord_7303991
  simp only [CollatzResearch.WordTrace]
  refine ⟨266398437281895504195543827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177598958187930336130362551 266398437281895504195543827)
  ·
    refine ⟨399597655922843256293315741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266398437281895504195543827 399597655922843256293315741)
    ·
      refine ⟨149849120971066221109993403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399597655922843256293315741 149849120971066221109993403)
      ·
        refine ⟨224773681456599331664990105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149849120971066221109993403 224773681456599331664990105)
        ·
          refine ⟨168580261092449498748742579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224773681456599331664990105 168580261092449498748742579)
          ·
            refine ⟨252870391638674248123113869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168580261092449498748742579 252870391638674248123113869)
            ·
              refine ⟨94826396864502843046167701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252870391638674248123113869 94826396864502843046167701)
              ·
                refine ⟨4444987353023570767789111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94826396864502843046167701 4444987353023570767789111)
                ·
                  refine ⟨6667481029535356151683667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444987353023570767789111 6667481029535356151683667)
                  ·
                    refine ⟨10001221544303034227525501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6667481029535356151683667 10001221544303034227525501)
                    ·
                      refine ⟨3750458079113637835322063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10001221544303034227525501 3750458079113637835322063)
                      ·
                        rfl

theorem cell23_7303991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_7303991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7303991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7303991 prefixEnd_7303991 := by exact prefixLift 7303991
  have htrace : WordTrace (prefixWord ++ tailWord_7303991) baseStart_7303991 baseEnd_7303991 := by
    simpa [prefixWord, tailWord_7303991, baseEnd_7303991] using wordTrace_append hprefix tailTrace_7303991
  have hstable : (prefixWord ++ tailWord_7303991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7303991).length < 2 ^ (prefixWord ++ tailWord_7303991).sum := by decide
  have hdescent : baseEnd_7303991 < baseStart_7303991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7303991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304048 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 1, 2, 2]
def baseStart_7304048 : Nat := 118140960795 + 7304048 * 2 ^ 59
def prefixEnd_7304048 : Nat := 4983230072969 + 3 ^ 40 * 7304048 * 2
def baseEnd_7304048 : Nat := 3750487347510944112309301

theorem tailTrace_7304048 : CollatzResearch.WordTrace tailWord_7304048 prefixEnd_7304048 3750487347510944112309301 := by
  unfold tailWord_7304048
  simp only [CollatzResearch.WordTrace]
  refine ⟨133200258121344501465184399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177600344161792668620245865 133200258121344501465184399)
  ·
    refine ⟨199800387182016752197776599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133200258121344501465184399 199800387182016752197776599)
    ·
      refine ⟨299700580773025128296664899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199800387182016752197776599 299700580773025128296664899)
      ·
        refine ⟨449550871159537692444997349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299700580773025128296664899 449550871159537692444997349)
        ·
          refine ⟨84290788342413317333437003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 449550871159537692444997349 84290788342413317333437003)
          ·
            refine ⟨126436182513619976000155505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84290788342413317333437003 126436182513619976000155505)
            ·
              refine ⟨94827136885214982000116629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126436182513619976000155505 94827136885214982000116629)
              ·
                refine ⟨4445022041494452281255467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94827136885214982000116629 4445022041494452281255467)
                ·
                  refine ⟨6667533062241678421883201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445022041494452281255467 6667533062241678421883201)
                  ·
                    refine ⟨5000649796681258816412401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667533062241678421883201 5000649796681258816412401)
                    ·
                      refine ⟨3750487347510944112309301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000649796681258816412401 3750487347510944112309301)
                      ·
                        rfl

theorem cell23_7304048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 2, 2].length) (baseStart_7304048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304048 prefixEnd_7304048 := by exact prefixLift 7304048
  have htrace : WordTrace (prefixWord ++ tailWord_7304048) baseStart_7304048 baseEnd_7304048 := by
    simpa [prefixWord, tailWord_7304048, baseEnd_7304048] using wordTrace_append hprefix tailTrace_7304048
  have hstable : (prefixWord ++ tailWord_7304048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304048).length < 2 ^ (prefixWord ++ tailWord_7304048).sum := by decide
  have hdescent : baseEnd_7304048 < baseStart_7304048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304054 : List Nat := [5, 1, 1, 3, 1, 1, 1, 10]
def baseStart_7304054 : Nat := 118140960795 + 7304054 * 2 ^ 59
def prefixEnd_7304054 : Nat := 4983230072969 + 3 ^ 40 * 7304054 * 2
def baseEnd_7304054 : Nat := 138907052903513744030899

theorem tailTrace_7304054 : CollatzResearch.WordTrace tailWord_7304054 prefixEnd_7304054 138907052903513744030899 := by
  unfold tailWord_7304054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16650045942541704122192951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177600490053778177303391477 16650045942541704122192951)
  ·
    refine ⟨24975068913812556183289427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16650045942541704122192951 24975068913812556183289427)
    ·
      refine ⟨37462603370718834274934141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24975068913812556183289427 37462603370718834274934141)
      ·
        refine ⟨14048476264019562853100303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37462603370718834274934141 14048476264019562853100303)
        ·
          refine ⟨21072714396029344279650455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048476264019562853100303 21072714396029344279650455)
          ·
            refine ⟨31609071594044016419475683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21072714396029344279650455 31609071594044016419475683)
            ·
              refine ⟨47413607391066024629213525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31609071594044016419475683 47413607391066024629213525)
              ·
                refine ⟨138907052903513744030899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47413607391066024629213525 138907052903513744030899)
                ·
                  rfl

theorem cell23_7304054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_7304054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304054 prefixEnd_7304054 := by exact prefixLift 7304054
  have htrace : WordTrace (prefixWord ++ tailWord_7304054) baseStart_7304054 baseEnd_7304054 := by
    simpa [prefixWord, tailWord_7304054, baseEnd_7304054] using wordTrace_append hprefix tailTrace_7304054
  have hstable : (prefixWord ++ tailWord_7304054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304054).length < 2 ^ (prefixWord ++ tailWord_7304054).sum := by decide
  have hdescent : baseEnd_7304054 < baseStart_7304054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304064 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3]
def baseStart_7304064 : Nat := 118140960795 + 7304064 * 2 ^ 59
def prefixEnd_7304064 : Nat := 4983230072969 + 3 ^ 40 * 7304064 * 2
def baseEnd_7304064 : Nat := 3750495563201416049709227

theorem tailTrace_7304064 : CollatzResearch.WordTrace tailWord_7304064 prefixEnd_7304064 3750495563201416049709227 := by
  unfold tailWord_7304064
  simp only [CollatzResearch.WordTrace]
  refine ⟨133200549905315518831475623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177600733207087358441967497 133200549905315518831475623)
  ·
    refine ⟨199800824857973278247213435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133200549905315518831475623 199800824857973278247213435)
    ·
      refine ⟨299701237286959917370820153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199800824857973278247213435 299701237286959917370820153)
      ·
        refine ⟨224775927965219938028115115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299701237286959917370820153 224775927965219938028115115)
        ·
          refine ⟨337163891947829907042172673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224775927965219938028115115 337163891947829907042172673)
          ·
            refine ⟨252872918960872430281629505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337163891947829907042172673 252872918960872430281629505)
            ·
              refine ⟨189654689220654322711222129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252872918960872430281629505 189654689220654322711222129)
              ·
                refine ⟨142241016915490742033416597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189654689220654322711222129 142241016915490742033416597)
                ·
                  refine ⟨6667547667913628532816403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142241016915490742033416597 6667547667913628532816403)
                  ·
                    refine ⟨10001321501870442799224605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6667547667913628532816403 10001321501870442799224605)
                    ·
                      refine ⟨3750495563201416049709227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10001321501870442799224605 3750495563201416049709227)
                      ·
                        rfl

theorem cell23_7304064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_7304064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304064 prefixEnd_7304064 := by exact prefixLift 7304064
  have htrace : WordTrace (prefixWord ++ tailWord_7304064) baseStart_7304064 baseEnd_7304064 := by
    simpa [prefixWord, tailWord_7304064, baseEnd_7304064] using wordTrace_append hprefix tailTrace_7304064
  have hstable : (prefixWord ++ tailWord_7304064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304064).length < 2 ^ (prefixWord ++ tailWord_7304064).sum := by decide
  have hdescent : baseEnd_7304064 < baseStart_7304064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304098 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_7304098 : Nat := 118140960795 + 7304098 * 2 ^ 59
def prefixEnd_7304098 : Nat := 4983230072969 + 3 ^ 40 * 7304098 * 2
def baseEnd_7304098 : Nat := 3750513021543668916684071

theorem tailTrace_7304098 : CollatzResearch.WordTrace tailWord_7304098 prefixEnd_7304098 3750513021543668916684071 := by
  unfold tailWord_7304098
  simp only [CollatzResearch.WordTrace]
  refine ⟨66600584973126965367422237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177601559928338574313125965 66600584973126965367422237)
  ·
    refine ⟨24975219364922612012783339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66600584973126965367422237 24975219364922612012783339)
    ·
      refine ⟨37462829047383918019175009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24975219364922612012783339 37462829047383918019175009)
      ·
        refine ⟨28097121785537938514381257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37462829047383918019175009 28097121785537938514381257)
        ·
          refine ⟨21072841339153453885785943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28097121785537938514381257 21072841339153453885785943)
          ·
            refine ⟨31609262008730180828678915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21072841339153453885785943 31609262008730180828678915)
            ·
              refine ⟨47413893013095271243018373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31609262008730180828678915 47413893013095271243018373)
              ·
                refine ⟨8890104939955363358065945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47413893013095271243018373 8890104939955363358065945)
                ·
                  refine ⟨6667578704966522518549459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890104939955363358065945 6667578704966522518549459)
                  ·
                    refine ⟨10001368057449783777824189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6667578704966522518549459 10001368057449783777824189)
                    ·
                      refine ⟨3750513021543668916684071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10001368057449783777824189 3750513021543668916684071)
                      ·
                        rfl

theorem cell23_7304098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_7304098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304098 prefixEnd_7304098 := by exact prefixLift 7304098
  have htrace : WordTrace (prefixWord ++ tailWord_7304098) baseStart_7304098 baseEnd_7304098 := by
    simpa [prefixWord, tailWord_7304098, baseEnd_7304098] using wordTrace_append hprefix tailTrace_7304098
  have hstable : (prefixWord ++ tailWord_7304098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304098).length < 2 ^ (prefixWord ++ tailWord_7304098).sum := by decide
  have hdescent : baseEnd_7304098 < baseStart_7304098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304121 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7304121 : Nat := 118140960795 + 7304121 * 2 ^ 59
def prefixEnd_7304121 : Nat := 4983230072969 + 3 ^ 40 * 7304121 * 2
def baseEnd_7304121 : Nat := 3750524831598722326696465

theorem tailTrace_7304121 : CollatzResearch.WordTrace tailWord_7304121 prefixEnd_7304121 3750524831598722326696465 := by
  unfold tailWord_7304121
  simp only [CollatzResearch.WordTrace]
  refine ⟨266403178771424536397776217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177602119180949690931850811 266403178771424536397776217)
  ·
    refine ⟨199802384078568402298332163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266403178771424536397776217 199802384078568402298332163)
    ·
      refine ⟨299703576117852603447498245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199802384078568402298332163 299703576117852603447498245)
      ·
        refine ⟨56194420522097363146405921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299703576117852603447498245 56194420522097363146405921)
        ·
          refine ⟨42145815391573022359804441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56194420522097363146405921 42145815391573022359804441)
          ·
            refine ⟨31609361543679766769853331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42145815391573022359804441 31609361543679766769853331)
            ·
              refine ⟨47414042315519650154779997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31609361543679766769853331 47414042315519650154779997)
              ·
                refine ⟨17780265868319868808042499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47414042315519650154779997 17780265868319868808042499)
                ·
                  refine ⟨26670398802479803212063749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17780265868319868808042499 26670398802479803212063749)
                  ·
                    refine ⟨5000699775464963102261953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26670398802479803212063749 5000699775464963102261953)
                    ·
                      refine ⟨3750524831598722326696465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000699775464963102261953 3750524831598722326696465)
                      ·
                        rfl

theorem cell23_7304121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7304121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304121 prefixEnd_7304121 := by exact prefixLift 7304121
  have htrace : WordTrace (prefixWord ++ tailWord_7304121) baseStart_7304121 baseEnd_7304121 := by
    simpa [prefixWord, tailWord_7304121, baseEnd_7304121] using wordTrace_append hprefix tailTrace_7304121
  have hstable : (prefixWord ++ tailWord_7304121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304121).length < 2 ^ (prefixWord ++ tailWord_7304121).sum := by decide
  have hdescent : baseEnd_7304121 < baseStart_7304121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304187 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 10]
def baseStart_7304187 : Nat := 118140960795 + 7304187 * 2 ^ 59
def prefixEnd_7304187 : Nat := 4983230072969 + 3 ^ 40 * 7304187 * 2
def baseEnd_7304187 : Nat := 1250186240440639689490387

theorem tailTrace_7304187 : CollatzResearch.WordTrace tailWord_7304187 prefixEnd_7304187 1250186240440639689490387 := by
  unfold tailWord_7304187
  simp only [CollatzResearch.WordTrace]
  refine ⟨266405585989185429669678815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177603723992790286446452543 266405585989185429669678815)
  ·
    refine ⟨399608378983778144504518223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266405585989185429669678815 399608378983778144504518223)
    ·
      refine ⟨599412568475667216756777335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399608378983778144504518223 599412568475667216756777335)
      ·
        refine ⟨899118852713500825135166003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599412568475667216756777335 899118852713500825135166003)
        ·
          refine ⟨1348678279070251237702749005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899118852713500825135166003 1348678279070251237702749005)
          ·
            refine ⟨505754354651344214138530877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1348678279070251237702749005 505754354651344214138530877)
            ·
              refine ⟨189657882994254080301949079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505754354651344214138530877 189657882994254080301949079)
              ·
                refine ⟨284486824491381120452923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189657882994254080301949079 284486824491381120452923619)
                ·
                  refine ⟨426730236737071680679385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284486824491381120452923619 426730236737071680679385429)
                  ·
                    refine ⟨1250186240440639689490387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 426730236737071680679385429 1250186240440639689490387)
                    ·
                      rfl

theorem cell23_7304187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_7304187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304187 prefixEnd_7304187 := by exact prefixLift 7304187
  have htrace : WordTrace (prefixWord ++ tailWord_7304187) baseStart_7304187 baseEnd_7304187 := by
    simpa [prefixWord, tailWord_7304187, baseEnd_7304187] using wordTrace_append hprefix tailTrace_7304187
  have hstable : (prefixWord ++ tailWord_7304187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304187).length < 2 ^ (prefixWord ++ tailWord_7304187).sum := by decide
  have hdescent : baseEnd_7304187 < baseStart_7304187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304248 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_7304248 : Nat := 118140960795 + 7304248 * 2 ^ 59
def prefixEnd_7304248 : Nat := 4983230072969 + 3 ^ 40 * 7304248 * 2
def baseEnd_7304248 : Nat := 3750590043641843329808381

theorem tailTrace_7304248 : CollatzResearch.WordTrace tailWord_7304248 prefixEnd_7304248 3750590043641843329808381 := by
  unfold tailWord_7304248
  simp only [CollatzResearch.WordTrace]
  refine ⟨133203905420982218543824699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177605207227976291391766265 133203905420982218543824699)
  ·
    refine ⟨199805858131473327815737049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133203905420982218543824699 199805858131473327815737049)
    ·
      refine ⟨149854393598604995861802787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199805858131473327815737049 149854393598604995861802787)
      ·
        refine ⟨224781590397907493792704181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149854393598604995861802787 224781590397907493792704181)
        ·
          refine ⟨21073274099803827543066017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224781590397907493792704181 21073274099803827543066017)
          ·
            refine ⟨15804955574852870657299513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21073274099803827543066017 15804955574852870657299513)
            ·
              refine ⟨11853716681139652992974635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15804955574852870657299513 11853716681139652992974635)
              ·
                refine ⟨17780575021709479489461953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11853716681139652992974635 17780575021709479489461953)
                ·
                  refine ⟨13335431266282109617096465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17780575021709479489461953 13335431266282109617096465)
                  ·
                    refine ⟨10001573449711582212822349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13335431266282109617096465 10001573449711582212822349)
                    ·
                      refine ⟨3750590043641843329808381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10001573449711582212822349 3750590043641843329808381)
                      ·
                        rfl

theorem cell23_7304248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_7304248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304248 prefixEnd_7304248 := by exact prefixLift 7304248
  have htrace : WordTrace (prefixWord ++ tailWord_7304248) baseStart_7304248 baseEnd_7304248 := by
    simpa [prefixWord, tailWord_7304248, baseEnd_7304248] using wordTrace_append hprefix tailTrace_7304248
  have hstable : (prefixWord ++ tailWord_7304248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304248).length < 2 ^ (prefixWord ++ tailWord_7304248).sum := by decide
  have hdescent : baseEnd_7304248 < baseStart_7304248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304311 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 4, 4]
def baseStart_7304311 : Nat := 118140960795 + 7304311 * 2 ^ 59
def prefixEnd_7304311 : Nat := 4983230072969 + 3 ^ 40 * 7304311 * 2
def baseEnd_7304311 : Nat := 1250207464307692194440197

theorem tailTrace_7304311 : CollatzResearch.WordTrace tailWord_7304311 prefixEnd_7304311 1250207464307692194440197 := by
  unfold tailWord_7304311
  simp only [CollatzResearch.WordTrace]
  refine ⟨266410108640736198847192787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177606739093824132564795191 266410108640736198847192787)
  ·
    refine ⟨399615162961104298270789181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266410108640736198847192787 399615162961104298270789181)
    ·
      refine ⟨149855686110414111851545943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399615162961104298270789181 149855686110414111851545943)
      ·
        refine ⟨224783529165621167777318915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149855686110414111851545943 224783529165621167777318915)
        ·
          refine ⟨337175293748431751665978373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224783529165621167777318915 337175293748431751665978373)
          ·
            refine ⟨63220367577830953437370945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337175293748431751665978373 63220367577830953437370945)
            ·
              refine ⟨47415275683373215078028209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63220367577830953437370945 47415275683373215078028209)
              ·
                refine ⟨35561456762529911308521157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47415275683373215078028209 35561456762529911308521157)
                ·
                  refine ⟨6667773142974358370347717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35561456762529911308521157 6667773142974358370347717)
                  ·
                    refine ⟨1250207464307692194440197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6667773142974358370347717 1250207464307692194440197)
                    ·
                      rfl

theorem cell23_7304311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_7304311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304311 prefixEnd_7304311 := by exact prefixLift 7304311
  have htrace : WordTrace (prefixWord ++ tailWord_7304311) baseStart_7304311 baseEnd_7304311 := by
    simpa [prefixWord, tailWord_7304311, baseEnd_7304311] using wordTrace_append hprefix tailTrace_7304311
  have hstable : (prefixWord ++ tailWord_7304311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304311).length < 2 ^ (prefixWord ++ tailWord_7304311).sum := by decide
  have hdescent : baseEnd_7304311 < baseStart_7304311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304338 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7304338 : Nat := 118140960795 + 7304338 * 2 ^ 59
def prefixEnd_7304338 : Nat := 4983230072969 + 3 ^ 40 * 7304338 * 2
def baseEnd_7304338 : Nat := 3750636256900747977682967

theorem tailTrace_7304338 : CollatzResearch.WordTrace tailWord_7304338 prefixEnd_7304338 3750636256900747977682967 := by
  unfold tailWord_7304338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66602773352909595614606417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177607395607758921638950445 66602773352909595614606417)
  ·
    refine ⟨49952080014682196710954813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66602773352909595614606417 49952080014682196710954813)
    ·
      refine ⟨18732030005505823766608055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49952080014682196710954813 18732030005505823766608055)
      ·
        refine ⟨28098045008258735649912083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18732030005505823766608055 28098045008258735649912083)
        ·
          refine ⟨42147067512388103474868125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28098045008258735649912083 42147067512388103474868125)
          ·
            refine ⟨15805150317145538803075547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42147067512388103474868125 15805150317145538803075547)
            ·
              refine ⟨23707725475718308204613321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15805150317145538803075547 23707725475718308204613321)
              ·
                refine ⟨17780794106788731153459991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23707725475718308204613321 17780794106788731153459991)
                ·
                  refine ⟨26671191160183096730189987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17780794106788731153459991 26671191160183096730189987)
                  ·
                    refine ⟨40006786740274645095284981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26671191160183096730189987 40006786740274645095284981)
                    ·
                      refine ⟨3750636256900747977682967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40006786740274645095284981 3750636256900747977682967)
                      ·
                        rfl

theorem cell23_7304338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7304338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304338 prefixEnd_7304338 := by exact prefixLift 7304338
  have htrace : WordTrace (prefixWord ++ tailWord_7304338) baseStart_7304338 baseEnd_7304338 := by
    simpa [prefixWord, tailWord_7304338, baseEnd_7304338] using wordTrace_append hprefix tailTrace_7304338
  have hstable : (prefixWord ++ tailWord_7304338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304338).length < 2 ^ (prefixWord ++ tailWord_7304338).sum := by decide
  have hdescent : baseEnd_7304338 < baseStart_7304338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304348 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7304348 : Nat := 118140960795 + 7304348 * 2 ^ 59
def prefixEnd_7304348 : Nat := 4983230072969 + 3 ^ 40 * 7304348 * 2
def baseEnd_7304348 : Nat := 3750641391707292938557921

theorem tailTrace_7304348 : CollatzResearch.WordTrace tailWord_7304348 prefixEnd_7304348 3750641391707292938557921 := by
  unfold tailWord_7304348
  simp only [CollatzResearch.WordTrace]
  refine ⟨133205729070801077083144849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177607638761068102777526465 133205729070801077083144849)
  ·
    refine ⟨99904296803100807812358637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133205729070801077083144849 99904296803100807812358637)
    ·
      refine ⟨37464111301162802929634489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99904296803100807812358637 37464111301162802929634489)
      ·
        refine ⟨28098083475872102197225867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37464111301162802929634489 28098083475872102197225867)
        ·
          refine ⟨42147125213808153295838801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28098083475872102197225867 42147125213808153295838801)
          ·
            refine ⟨31610343910356114971879101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42147125213808153295838801 31610343910356114971879101)
            ·
              refine ⟨11853878966383543114454663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31610343910356114971879101 11853878966383543114454663)
              ·
                refine ⟨17780818449575314671681995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11853878966383543114454663 17780818449575314671681995)
                ·
                  refine ⟨26671227674362972007522993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17780818449575314671681995 26671227674362972007522993)
                  ·
                    refine ⟨20003420755772229005642245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26671227674362972007522993 20003420755772229005642245)
                    ·
                      refine ⟨3750641391707292938557921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20003420755772229005642245 3750641391707292938557921)
                      ·
                        rfl

theorem cell23_7304348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7304348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304348 prefixEnd_7304348 := by exact prefixLift 7304348
  have htrace : WordTrace (prefixWord ++ tailWord_7304348) baseStart_7304348 baseEnd_7304348 := by
    simpa [prefixWord, tailWord_7304348, baseEnd_7304348] using wordTrace_append hprefix tailTrace_7304348
  have hstable : (prefixWord ++ tailWord_7304348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304348).length < 2 ^ (prefixWord ++ tailWord_7304348).sum := by decide
  have hdescent : baseEnd_7304348 < baseStart_7304348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304369 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7304369 : Nat := 118140960795 + 7304369 * 2 ^ 59
def prefixEnd_7304369 : Nat := 4983230072969 + 3 ^ 40 * 7304369 * 2
def baseEnd_7304369 : Nat := 3750652174801037356395325

theorem tailTrace_7304369 : CollatzResearch.WordTrace tailWord_7304369 prefixEnd_7304369 3750652174801037356395325 := by
  unfold tailWord_7304369
  simp only [CollatzResearch.WordTrace]
  refine ⟨266412224074526074752804161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177608149383017383168536107 266412224074526074752804161)
  ·
    refine ⟨199809168055894556064603121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266412224074526074752804161 199809168055894556064603121)
    ·
      refine ⟨149856876041920917048452341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199809168055894556064603121 149856876041920917048452341)
      ·
        refine ⟨14049082128930085973292407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149856876041920917048452341 14049082128930085973292407)
        ·
          refine ⟨21073623193395128959938611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14049082128930085973292407 21073623193395128959938611)
          ·
            refine ⟨31610434790092693439907917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21073623193395128959938611 31610434790092693439907917)
            ·
              refine ⟨11853913046284760039965469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31610434790092693439907917 11853913046284760039965469)
              ·
                refine ⟨4445217392356785014987051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11853913046284760039965469 4445217392356785014987051)
                ·
                  refine ⟨6667826088535177522480577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445217392356785014987051 6667826088535177522480577)
                  ·
                    refine ⟨5000869566401383141860433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667826088535177522480577 5000869566401383141860433)
                    ·
                      refine ⟨3750652174801037356395325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000869566401383141860433 3750652174801037356395325)
                      ·
                        rfl

theorem cell23_7304369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7304369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304369 prefixEnd_7304369 := by exact prefixLift 7304369
  have htrace : WordTrace (prefixWord ++ tailWord_7304369) baseStart_7304369 baseEnd_7304369 := by
    simpa [prefixWord, tailWord_7304369, baseEnd_7304369] using wordTrace_append hprefix tailTrace_7304369
  have hstable : (prefixWord ++ tailWord_7304369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304369).length < 2 ^ (prefixWord ++ tailWord_7304369).sum := by decide
  have hdescent : baseEnd_7304369 < baseStart_7304369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304378 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_7304378 : Nat := 118140960795 + 7304378 * 2 ^ 59
def prefixEnd_7304378 : Nat := 4983230072969 + 3 ^ 40 * 7304378 * 2
def baseEnd_7304378 : Nat := 3750656796126927821182783

theorem tailTrace_7304378 : CollatzResearch.WordTrace tailWord_7304378 prefixEnd_7304378 3750656796126927821182783 := by
  unfold tailWord_7304378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66603138082873367322470447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177608368220995646193254525 66603138082873367322470447)
  ·
    refine ⟨99904707124310050983705671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66603138082873367322470447 99904707124310050983705671)
    ·
      refine ⟨149857060686465076475558507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99904707124310050983705671 149857060686465076475558507)
      ·
        refine ⟨224785591029697614713337761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149857060686465076475558507 224785591029697614713337761)
        ·
          refine ⟨168589193272273211035003321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224785591029697614713337761 168589193272273211035003321)
          ·
            refine ⟨126441894954204908276252491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168589193272273211035003321 126441894954204908276252491)
            ·
              refine ⟨189662842431307362414378737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126441894954204908276252491 189662842431307362414378737)
              ·
                refine ⟨142247131823480521810784053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189662842431307362414378737 142247131823480521810784053)
                ·
                  refine ⟨13335668608451298919761005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142247131823480521810784053 13335668608451298919761005)
                  ·
                    refine ⟨5000875728169237094910377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13335668608451298919761005 5000875728169237094910377)
                    ·
                      refine ⟨3750656796126927821182783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000875728169237094910377 3750656796126927821182783)
                      ·
                        rfl

theorem cell23_7304378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_7304378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304378 prefixEnd_7304378 := by exact prefixLift 7304378
  have htrace : WordTrace (prefixWord ++ tailWord_7304378) baseStart_7304378 baseEnd_7304378 := by
    simpa [prefixWord, tailWord_7304378, baseEnd_7304378] using wordTrace_append hprefix tailTrace_7304378
  have hstable : (prefixWord ++ tailWord_7304378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304378).length < 2 ^ (prefixWord ++ tailWord_7304378).sum := by decide
  have hdescent : baseEnd_7304378 < baseStart_7304378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304406 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7304406 : Nat := 118140960795 + 7304406 * 2 ^ 59
def prefixEnd_7304406 : Nat := 4983230072969 + 3 ^ 40 * 7304406 * 2
def baseEnd_7304406 : Nat := 3750671173585253711632655

theorem tailTrace_7304406 : CollatzResearch.WordTrace tailWord_7304406 prefixEnd_7304406 3750671173585253711632655 := by
  unfold tailWord_7304406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16650848348462001879493817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177609049050261353381267381 16650848348462001879493817)
  ·
    refine ⟨12488136261346501409620363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16650848348462001879493817 12488136261346501409620363)
    ·
      refine ⟨18732204392019752114430545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12488136261346501409620363 18732204392019752114430545)
      ·
        refine ⟨14049153294014814085822909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18732204392019752114430545 14049153294014814085822909)
        ·
          refine ⟨5268432485255555282183591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14049153294014814085822909 5268432485255555282183591)
          ·
            refine ⟨7902648727883332923275387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268432485255555282183591 7902648727883332923275387)
            ·
              refine ⟨11853973091824999384913081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902648727883332923275387 11853973091824999384913081)
              ·
                refine ⟨8890479818868749538684811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11853973091824999384913081 8890479818868749538684811)
                ·
                  refine ⟨13335719728303124308027217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890479818868749538684811 13335719728303124308027217)
                  ·
                    refine ⟨10001789796227343231020413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13335719728303124308027217 10001789796227343231020413)
                    ·
                      refine ⟨3750671173585253711632655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10001789796227343231020413 3750671173585253711632655)
                      ·
                        rfl

theorem cell23_7304406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7304406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304406 prefixEnd_7304406 := by exact prefixLift 7304406
  have htrace : WordTrace (prefixWord ++ tailWord_7304406) baseStart_7304406 baseEnd_7304406 := by
    simpa [prefixWord, tailWord_7304406, baseEnd_7304406] using wordTrace_append hprefix tailTrace_7304406
  have hstable : (prefixWord ++ tailWord_7304406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304406).length < 2 ^ (prefixWord ++ tailWord_7304406).sum := by decide
  have hdescent : baseEnd_7304406 < baseStart_7304406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304429 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7304429 : Nat := 118140960795 + 7304429 * 2 ^ 59
def prefixEnd_7304429 : Nat := 4983230072969 + 3 ^ 40 * 7304429 * 2
def baseEnd_7304429 : Nat := 3750682983640307121645049

theorem tailTrace_7304429 : CollatzResearch.WordTrace tailWord_7304429 prefixEnd_7304429 3750682983640307121645049 := by
  unfold tailWord_7304429
  simp only [CollatzResearch.WordTrace]
  refine ⟨266414412454308704999988341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177609608302872469999992227 266414412454308704999988341)
  ·
    refine ⟨24976351167591441093748907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266414412454308704999988341 24976351167591441093748907)
    ·
      refine ⟨37464526751387161640623361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24976351167591441093748907 37464526751387161640623361)
      ·
        refine ⟨28098395063540371230467521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37464526751387161640623361 28098395063540371230467521)
        ·
          refine ⟨21073796297655278422850641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28098395063540371230467521 21073796297655278422850641)
          ·
            refine ⟨15805347223241458817137981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21073796297655278422850641 15805347223241458817137981)
            ·
              refine ⟨5927005208715547056426743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15805347223241458817137981 5927005208715547056426743)
              ·
                refine ⟨8890507813073320584640115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927005208715547056426743 8890507813073320584640115)
                ·
                  refine ⟨13335761719609980876960173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890507813073320584640115 13335761719609980876960173)
                  ·
                    refine ⟨5000910644853742828860065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13335761719609980876960173 5000910644853742828860065)
                    ·
                      refine ⟨3750682983640307121645049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000910644853742828860065 3750682983640307121645049)
                      ·
                        rfl

theorem cell23_7304429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7304429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304429 prefixEnd_7304429 := by exact prefixLift 7304429
  have htrace : WordTrace (prefixWord ++ tailWord_7304429) baseStart_7304429 baseEnd_7304429 := by
    simpa [prefixWord, tailWord_7304429, baseEnd_7304429] using wordTrace_append hprefix tailTrace_7304429
  have hstable : (prefixWord ++ tailWord_7304429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304429).length < 2 ^ (prefixWord ++ tailWord_7304429).sum := by decide
  have hdescent : baseEnd_7304429 < baseStart_7304429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304438 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7304438 : Nat := 118140960795 + 7304438 * 2 ^ 59
def prefixEnd_7304438 : Nat := 4983230072969 + 3 ^ 40 * 7304438 * 2
def baseEnd_7304438 : Nat := 3750687604966197586432507

theorem tailTrace_7304438 : CollatzResearch.WordTrace tailWord_7304438 prefixEnd_7304438 3750687604966197586432507 := by
  unfold tailWord_7304438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16650921294454756221066623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177609827140850733024710645 16650921294454756221066623)
  ·
    refine ⟨24976381941682134331599935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16650921294454756221066623 24976381941682134331599935)
    ·
      refine ⟨37464572912523201497399903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24976381941682134331599935 37464572912523201497399903)
      ·
        refine ⟨56196859368784802246099855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37464572912523201497399903 56196859368784802246099855)
        ·
          refine ⟨84295289053177203369149783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56196859368784802246099855 84295289053177203369149783)
          ·
            refine ⟨126442933579765805053724675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84295289053177203369149783 126442933579765805053724675)
            ·
              refine ⟨189664400369648707580587013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126442933579765805053724675 189664400369648707580587013)
              ·
                refine ⟨35562075069309132671360065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189664400369648707580587013 35562075069309132671360065)
                ·
                  refine ⟨26671556301981849503520049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35562075069309132671360065 26671556301981849503520049)
                  ·
                    refine ⟨20003667226486387127640037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26671556301981849503520049 20003667226486387127640037)
                    ·
                      refine ⟨3750687604966197586432507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20003667226486387127640037 3750687604966197586432507)
                      ·
                        rfl

theorem cell23_7304438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7304438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304438 prefixEnd_7304438 := by exact prefixLift 7304438
  have htrace : WordTrace (prefixWord ++ tailWord_7304438) baseStart_7304438 baseEnd_7304438 := by
    simpa [prefixWord, tailWord_7304438, baseEnd_7304438] using wordTrace_append hprefix tailTrace_7304438
  have hstable : (prefixWord ++ tailWord_7304438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304438).length < 2 ^ (prefixWord ++ tailWord_7304438).sum := by decide
  have hdescent : baseEnd_7304438 < baseStart_7304438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304442 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_7304442 : Nat := 118140960795 + 7304442 * 2 ^ 59
def prefixEnd_7304442 : Nat := 4983230072969 + 3 ^ 40 * 7304442 * 2
def baseEnd_7304442 : Nat := 3750689658888815570782489

theorem tailTrace_7304442 : CollatzResearch.WordTrace tailWord_7304442 prefixEnd_7304442 3750689658888815570782489 := by
  unfold tailWord_7304442
  simp only [CollatzResearch.WordTrace]
  refine ⟨66603721650815402055052895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177609924402174405480141053 66603721650815402055052895)
  ·
    refine ⟨99905582476223103082579343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66603721650815402055052895 99905582476223103082579343)
    ·
      refine ⟨149858373714334654623869015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99905582476223103082579343 149858373714334654623869015)
      ·
        refine ⟨224787560571501981935803523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149858373714334654623869015 224787560571501981935803523)
        ·
          refine ⟨337181340857252972903705285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224787560571501981935803523 337181340857252972903705285)
          ·
            refine ⟨63221501410734932419444741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337181340857252972903705285 63221501410734932419444741)
            ·
              refine ⟨11854031514512799828645889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63221501410734932419444741 11854031514512799828645889)
              ·
                refine ⟨8890523635884599871484417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11854031514512799828645889 8890523635884599871484417)
                ·
                  refine ⟨6667892726913449903613313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890523635884599871484417 6667892726913449903613313)
                  ·
                    refine ⟨5000919545185087427709985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6667892726913449903613313 5000919545185087427709985)
                    ·
                      refine ⟨3750689658888815570782489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5000919545185087427709985 3750689658888815570782489)
                      ·
                        rfl

theorem cell23_7304442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_7304442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304442 prefixEnd_7304442 := by exact prefixLift 7304442
  have htrace : WordTrace (prefixWord ++ tailWord_7304442) baseStart_7304442 baseEnd_7304442 := by
    simpa [prefixWord, tailWord_7304442, baseEnd_7304442] using wordTrace_append hprefix tailTrace_7304442
  have hstable : (prefixWord ++ tailWord_7304442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304442).length < 2 ^ (prefixWord ++ tailWord_7304442).sum := by decide
  have hdescent : baseEnd_7304442 < baseStart_7304442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304482 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7304482 : Nat := 118140960795 + 7304482 * 2 ^ 59
def prefixEnd_7304482 : Nat := 4983230072969 + 3 ^ 40 * 7304482 * 2
def baseEnd_7304482 : Nat := 416745577568332823809145

theorem tailTrace_7304482 : CollatzResearch.WordTrace tailWord_7304482 prefixEnd_7304482 416745577568332823809145 := by
  unfold tailWord_7304482
  simp only [CollatzResearch.WordTrace]
  refine ⟨66604086380779173762916925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177610897015411130034445133 66604086380779173762916925)
  ·
    refine ⟨24976532392792190161093847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66604086380779173762916925 24976532392792190161093847)
    ·
      refine ⟨37464798589188285241640771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24976532392792190161093847 37464798589188285241640771)
      ·
        refine ⟨56197197883782427862461157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37464798589188285241640771 56197197883782427862461157)
        ·
          refine ⟨10536974603209205224211467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56197197883782427862461157 10536974603209205224211467)
          ·
            refine ⟨15805461904813807836317201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536974603209205224211467 15805461904813807836317201)
            ·
              refine ⟨11854096428610355877237901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15805461904813807836317201 11854096428610355877237901)
              ·
                refine ⟨4445286160728883453964213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11854096428610355877237901 4445286160728883453964213)
                ·
                  refine ⟨416745577568332823809145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4445286160728883453964213 416745577568332823809145)
                  ·
                    rfl

theorem cell23_7304482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7304482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304482 prefixEnd_7304482 := by exact prefixLift 7304482
  have htrace : WordTrace (prefixWord ++ tailWord_7304482) baseStart_7304482 baseEnd_7304482 := by
    simpa [prefixWord, tailWord_7304482, baseEnd_7304482] using wordTrace_append hprefix tailTrace_7304482
  have hstable : (prefixWord ++ tailWord_7304482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304482).length < 2 ^ (prefixWord ++ tailWord_7304482).sum := by decide
  have hdescent : baseEnd_7304482 < baseStart_7304482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304552 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7304552 : Nat := 118140960795 + 7304552 * 2 ^ 59
def prefixEnd_7304552 : Nat := 4983230072969 + 3 ^ 40 * 7304552 * 2
def baseEnd_7304552 : Nat := 3750746141760810140406983

theorem tailTrace_7304552 : CollatzResearch.WordTrace tailWord_7304552 prefixEnd_7304552 3750746141760810140406983 := by
  unfold tailWord_7304552
  simp only [CollatzResearch.WordTrace]
  refine ⟨133209449316431548503357955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177612599088575398004477273 133209449316431548503357955)
  ·
    refine ⟨199814173974647322755036933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133209449316431548503357955 199814173974647322755036933)
    ·
      refine ⟨37465157620246373016569425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199814173974647322755036933 37465157620246373016569425)
      ·
        refine ⟨28098868215184779762427069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37465157620246373016569425 28098868215184779762427069)
        ·
          refine ⟨10537075580694292410910151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28098868215184779762427069 10537075580694292410910151)
          ·
            refine ⟨15805613371041438616365227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537075580694292410910151 15805613371041438616365227)
            ·
              refine ⟨23708420056562157924547841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15805613371041438616365227 23708420056562157924547841)
              ·
                refine ⟨17781315042421618443410881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23708420056562157924547841 17781315042421618443410881)
                ·
                  refine ⟨13335986281816213832558161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17781315042421618443410881 13335986281816213832558161)
                  ·
                    refine ⟨10001989711362160374418621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13335986281816213832558161 10001989711362160374418621)
                    ·
                      refine ⟨3750746141760810140406983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10001989711362160374418621 3750746141760810140406983)
                      ·
                        rfl

theorem cell23_7304552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7304552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304552 prefixEnd_7304552 := by exact prefixLift 7304552
  have htrace : WordTrace (prefixWord ++ tailWord_7304552) baseStart_7304552 baseEnd_7304552 := by
    simpa [prefixWord, tailWord_7304552, baseEnd_7304552] using wordTrace_append hprefix tailTrace_7304552
  have hstable : (prefixWord ++ tailWord_7304552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304552).length < 2 ^ (prefixWord ++ tailWord_7304552).sum := by decide
  have hdescent : baseEnd_7304552 < baseStart_7304552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304585 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_7304585 : Nat := 118140960795 + 7304585 * 2 ^ 59
def prefixEnd_7304585 : Nat := 4983230072969 + 3 ^ 40 * 7304585 * 2
def baseEnd_7304585 : Nat := 1250254362207469503764777

theorem tailTrace_7304585 : CollatzResearch.WordTrace tailWord_7304585 prefixEnd_7304585 1250254362207469503764777 := by
  unfold tailWord_7304585
  simp only [CollatzResearch.WordTrace]
  refine ⟨266420102241743543642667209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177613401494495695761778139 266420102241743543642667209)
  ·
    refine ⟨199815076681307657732000407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266420102241743543642667209 199815076681307657732000407)
    ·
      refine ⟨299722615021961486598000611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199815076681307657732000407 299722615021961486598000611)
      ·
        refine ⟨449583922532942229897000917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299722615021961486598000611 449583922532942229897000917)
        ·
          refine ⟨10537123184365833513210959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 449583922532942229897000917 10537123184365833513210959)
          ·
            refine ⟨15805684776548750269816439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537123184365833513210959 15805684776548750269816439)
            ·
              refine ⟨23708527164823125404724659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15805684776548750269816439 23708527164823125404724659)
              ·
                refine ⟨35562790747234688107086989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23708527164823125404724659 35562790747234688107086989)
                ·
                  refine ⟨13336046530213008040157621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35562790747234688107086989 13336046530213008040157621)
                  ·
                    refine ⟨1250254362207469503764777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13336046530213008040157621 1250254362207469503764777)
                    ·
                      rfl

theorem cell23_7304585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_7304585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304585 prefixEnd_7304585 := by exact prefixLift 7304585
  have htrace : WordTrace (prefixWord ++ tailWord_7304585) baseStart_7304585 baseEnd_7304585 := by
    simpa [prefixWord, tailWord_7304585, baseEnd_7304585] using wordTrace_append hprefix tailTrace_7304585
  have hstable : (prefixWord ++ tailWord_7304585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304585).length < 2 ^ (prefixWord ++ tailWord_7304585).sum := by decide
  have hdescent : baseEnd_7304585 < baseStart_7304585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304602 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_7304602 : Nat := 118140960795 + 7304602 * 2 ^ 59
def prefixEnd_7304602 : Nat := 4983230072969 + 3 ^ 40 * 7304602 * 2
def baseEnd_7304602 : Nat := 1250257271931178314927251

theorem tailTrace_7304602 : CollatzResearch.WordTrace tailWord_7304602 prefixEnd_7304602 1250257271931178314927251 := by
  unfold tailWord_7304602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66605180570670488886509015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177613814855121303697357373 66605180570670488886509015)
  ·
    refine ⟨99907770856005733329763523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66605180570670488886509015 99907770856005733329763523)
    ·
      refine ⟨149861656284008599994645285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99907770856005733329763523 149861656284008599994645285)
      ·
        refine ⟨28099060553251612498995991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149861656284008599994645285 28099060553251612498995991)
        ·
          refine ⟨42148590829877418748493987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28099060553251612498995991 42148590829877418748493987)
          ·
            refine ⟨63222886244816128122740981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42148590829877418748493987 63222886244816128122740981)
            ·
              refine ⟨5927145585451512011506967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63222886244816128122740981 5927145585451512011506967)
              ·
                refine ⟨8890718378177268017260451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927145585451512011506967 8890718378177268017260451)
                ·
                  refine ⟨13336077567265902025890677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890718378177268017260451 13336077567265902025890677)
                  ·
                    refine ⟨1250257271931178314927251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13336077567265902025890677 1250257271931178314927251)
                    ·
                      rfl

theorem cell23_7304602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_7304602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304602 prefixEnd_7304602 := by exact prefixLift 7304602
  have htrace : WordTrace (prefixWord ++ tailWord_7304602) baseStart_7304602 baseEnd_7304602 := by
    simpa [prefixWord, tailWord_7304602, baseEnd_7304602] using wordTrace_append hprefix tailTrace_7304602
  have hstable : (prefixWord ++ tailWord_7304602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304602).length < 2 ^ (prefixWord ++ tailWord_7304602).sum := by decide
  have hdescent : baseEnd_7304602 < baseStart_7304602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304625 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7304625 : Nat := 118140960795 + 7304625 * 2 ^ 59
def prefixEnd_7304625 : Nat := 4983230072969 + 3 ^ 40 * 7304625 * 2
def baseEnd_7304625 : Nat := 3750783625848588354794147

theorem tailTrace_7304625 : CollatzResearch.WordTrace tailWord_7304625 prefixEnd_7304625 3750783625848588354794147 := by
  unfold tailWord_7304625
  simp only [CollatzResearch.WordTrace]
  refine ⟨266421561161598630474123329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177614374107732420316082219 266421561161598630474123329)
  ·
    refine ⟨199816170871198972855592497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266421561161598630474123329 199816170871198972855592497)
    ·
      refine ⟨149862128153399229641694373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199816170871198972855592497 149862128153399229641694373)
      ·
        refine ⟨28099149028762355557817695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149862128153399229641694373 28099149028762355557817695)
        ·
          refine ⟨42148723543143533336726543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28099149028762355557817695 42148723543143533336726543)
          ·
            refine ⟨63223085314715300005089815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42148723543143533336726543 63223085314715300005089815)
            ·
              refine ⟨94834627972072950007634723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63223085314715300005089815 94834627972072950007634723)
              ·
                refine ⟨142251941958109425011452085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94834627972072950007634723 142251941958109425011452085)
                ·
                  refine ⟨13336119558572758594823633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142251941958109425011452085 13336119558572758594823633)
                  ·
                    refine ⟨10002089668929568946117725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13336119558572758594823633 10002089668929568946117725)
                    ·
                      refine ⟨3750783625848588354794147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10002089668929568946117725 3750783625848588354794147)
                      ·
                        rfl

theorem cell23_7304625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7304625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304625 prefixEnd_7304625 := by exact prefixLift 7304625
  have htrace : WordTrace (prefixWord ++ tailWord_7304625) baseStart_7304625 baseEnd_7304625 := by
    simpa [prefixWord, tailWord_7304625, baseEnd_7304625] using wordTrace_append hprefix tailTrace_7304625
  have hstable : (prefixWord ++ tailWord_7304625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304625).length < 2 ^ (prefixWord ++ tailWord_7304625).sum := by decide
  have hdescent : baseEnd_7304625 < baseStart_7304625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304655 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_7304655 : Nat := 118140960795 + 7304655 * 2 ^ 59
def prefixEnd_7304655 : Nat := 4983230072969 + 3 ^ 40 * 7304655 * 2
def baseEnd_7304655 : Nat := 3750799030268223237419009

theorem tailTrace_7304655 : CollatzResearch.WordTrace tailWord_7304655 prefixEnd_7304655 3750799030268223237419009 := by
  unfold tailWord_7304655
  simp only [CollatzResearch.WordTrace]
  refine ⟨266422655351489945597715419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177615103567659963731810279 266422655351489945597715419)
  ·
    refine ⟨399633983027234918396573129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266422655351489945597715419 399633983027234918396573129)
    ·
      refine ⟨299725487270426188797429847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399633983027234918396573129 299725487270426188797429847)
      ·
        refine ⟨449588230905639283196144771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299725487270426188797429847 449588230905639283196144771)
        ·
          refine ⟨674382346358458924794217157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449588230905639283196144771 674382346358458924794217157)
          ·
            refine ⟨126446689942211048398915717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 674382346358458924794217157 126446689942211048398915717)
            ·
              refine ⟨23708754364164571574796697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126446689942211048398915717 23708754364164571574796697)
              ·
                refine ⟨17781565773123428681097523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23708754364164571574796697 17781565773123428681097523)
                ·
                  refine ⟨26672348659685143021646285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17781565773123428681097523 26672348659685143021646285)
                  ·
                    refine ⟨10002130747381928633117357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26672348659685143021646285 10002130747381928633117357)
                    ·
                      refine ⟨3750799030268223237419009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10002130747381928633117357 3750799030268223237419009)
                      ·
                        rfl

theorem cell23_7304655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_7304655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304655 prefixEnd_7304655 := by exact prefixLift 7304655
  have htrace : WordTrace (prefixWord ++ tailWord_7304655) baseStart_7304655 baseEnd_7304655 := by
    simpa [prefixWord, tailWord_7304655, baseEnd_7304655] using wordTrace_append hprefix tailTrace_7304655
  have hstable : (prefixWord ++ tailWord_7304655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304655).length < 2 ^ (prefixWord ++ tailWord_7304655).sum := by decide
  have hdescent : baseEnd_7304655 < baseStart_7304655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304672 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3]
def baseStart_7304672 : Nat := 118140960795 + 7304672 * 2 ^ 59
def prefixEnd_7304672 : Nat := 4983230072969 + 3 ^ 40 * 7304672 * 2
def baseEnd_7304672 : Nat := 3750807759439349670906431

theorem tailTrace_7304672 : CollatzResearch.WordTrace tailWord_7304672 prefixEnd_7304672 3750807759439349670906431 := by
  unfold tailWord_7304672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133211637696214178750542135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177615516928285571667389513 133211637696214178750542135)
  ·
    refine ⟨199817456544321268125813203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133211637696214178750542135 199817456544321268125813203)
    ·
      refine ⟨299726184816481902188719805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199817456544321268125813203 299726184816481902188719805)
      ·
        refine ⟨112397319306180713320769927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299726184816481902188719805 112397319306180713320769927)
        ·
          refine ⟨168595978959271069981154891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112397319306180713320769927 168595978959271069981154891)
          ·
            refine ⟨252893968438906604971732337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168595978959271069981154891 252893968438906604971732337)
            ·
              refine ⟨189670476329179953728799253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252893968438906604971732337 189670476329179953728799253)
              ·
                refine ⟨8890803577930310331037465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189670476329179953728799253 8890803577930310331037465)
                ·
                  refine ⟨6668102683447732748278099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890803577930310331037465 6668102683447732748278099)
                  ·
                    refine ⟨10002154025171599122417149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668102683447732748278099 10002154025171599122417149)
                    ·
                      refine ⟨3750807759439349670906431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10002154025171599122417149 3750807759439349670906431)
                      ·
                        rfl

theorem cell23_7304672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_7304672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304672 prefixEnd_7304672 := by exact prefixLift 7304672
  have htrace : WordTrace (prefixWord ++ tailWord_7304672) baseStart_7304672 baseEnd_7304672 := by
    simpa [prefixWord, tailWord_7304672, baseEnd_7304672] using wordTrace_append hprefix tailTrace_7304672
  have hstable : (prefixWord ++ tailWord_7304672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304672).length < 2 ^ (prefixWord ++ tailWord_7304672).sum := by decide
  have hdescent : baseEnd_7304672 < baseStart_7304672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304712 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_7304712 : Nat := 118140960795 + 7304712 * 2 ^ 59
def prefixEnd_7304712 : Nat := 4983230072969 + 3 ^ 40 * 7304712 * 2
def baseEnd_7304712 : Nat := 3750828298665529514406247

theorem tailTrace_7304712 : CollatzResearch.WordTrace tailWord_7304712 prefixEnd_7304712 3750828298665529514406247 := by
  unfold tailWord_7304712
  simp only [CollatzResearch.WordTrace]
  refine ⟨133212367156141722166270195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177616489541522296221693593 133212367156141722166270195)
  ·
    refine ⟨199818550734212583249405293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133212367156141722166270195 199818550734212583249405293)
    ·
      refine ⟨74931956525329718718526985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199818550734212583249405293 74931956525329718718526985)
      ·
        refine ⟨56198967393997289038895239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74931956525329718718526985 56198967393997289038895239)
        ·
          refine ⟨84298451090995933558342859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56198967393997289038895239 84298451090995933558342859)
          ·
            refine ⟨126447676636493900337514289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84298451090995933558342859 126447676636493900337514289)
            ·
              refine ⟨94835757477370425253135717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126447676636493900337514289 94835757477370425253135717)
              ·
                refine ⟨17781704527006954734962947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94835757477370425253135717 17781704527006954734962947)
                ·
                  refine ⟨26672556790510432102444421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17781704527006954734962947 26672556790510432102444421)
                  ·
                    refine ⟨5001104398220706019208329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26672556790510432102444421 5001104398220706019208329)
                    ·
                      refine ⟨3750828298665529514406247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001104398220706019208329 3750828298665529514406247)
                      ·
                        rfl

theorem cell23_7304712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_7304712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304712 prefixEnd_7304712 := by exact prefixLift 7304712
  have htrace : WordTrace (prefixWord ++ tailWord_7304712) baseStart_7304712 baseEnd_7304712 := by
    simpa [prefixWord, tailWord_7304712, baseEnd_7304712] using wordTrace_append hprefix tailTrace_7304712
  have hstable : (prefixWord ++ tailWord_7304712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304712).length < 2 ^ (prefixWord ++ tailWord_7304712).sum := by decide
  have hdescent : baseEnd_7304712 < baseStart_7304712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304735 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 7]
def baseStart_7304735 : Nat := 118140960795 + 7304735 * 2 ^ 59
def prefixEnd_7304735 : Nat := 4983230072969 + 3 ^ 40 * 7304735 * 2
def baseEnd_7304735 : Nat := 416760012080064769379849

theorem tailTrace_7304735 : CollatzResearch.WordTrace tailWord_7304735 prefixEnd_7304735 416760012080064769379849 := by
  unfold tailWord_7304735
  simp only [CollatzResearch.WordTrace]
  refine ⟨266425573191200119260627659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177617048794133412840418439 266425573191200119260627659)
  ·
    refine ⟨399638359786800178890941489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266425573191200119260627659 399638359786800178890941489)
    ·
      refine ⟨299728769840100134168206117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399638359786800178890941489 299728769840100134168206117)
      ·
        refine ⟨56199144345018775156538647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299728769840100134168206117 56199144345018775156538647)
        ·
          refine ⟨84298716517528162734807971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56199144345018775156538647 84298716517528162734807971)
          ·
            refine ⟨126448074776292244102211957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84298716517528162734807971 126448074776292244102211957)
            ·
              refine ⟨11854507010277397884582371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126448074776292244102211957 11854507010277397884582371)
              ·
                refine ⟨17781760515416096826873557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11854507010277397884582371 17781760515416096826873557)
                ·
                  refine ⟨416760012080064769379849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17781760515416096826873557 416760012080064769379849)
                  ·
                    rfl

theorem cell23_7304735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 7].length) (baseStart_7304735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304735 prefixEnd_7304735 := by exact prefixLift 7304735
  have htrace : WordTrace (prefixWord ++ tailWord_7304735) baseStart_7304735 baseEnd_7304735 := by
    simpa [prefixWord, tailWord_7304735, baseEnd_7304735] using wordTrace_append hprefix tailTrace_7304735
  have hstable : (prefixWord ++ tailWord_7304735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304735).length < 2 ^ (prefixWord ++ tailWord_7304735).sum := by decide
  have hdescent : baseEnd_7304735 < baseStart_7304735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304746 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7304746 : Nat := 118140960795 + 7304746 * 2 ^ 59
def prefixEnd_7304746 : Nat := 4983230072969 + 3 ^ 40 * 7304746 * 2
def baseEnd_7304746 : Nat := 3750845757007782381381091

theorem tailTrace_7304746 : CollatzResearch.WordTrace tailWord_7304746 prefixEnd_7304746 3750845757007782381381091 := by
  unfold tailWord_7304746
  simp only [CollatzResearch.WordTrace]
  refine ⟨66606493598540067034819523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177617316262773512092852061 66606493598540067034819523)
  ·
    refine ⟨99909740397810100552229285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66606493598540067034819523 99909740397810100552229285)
    ·
      refine ⟨18733076324589393853542991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99909740397810100552229285 18733076324589393853542991)
      ·
        refine ⟨28099614486884090780314487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18733076324589393853542991 28099614486884090780314487)
        ·
          refine ⟨42149421730326136170471731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28099614486884090780314487 42149421730326136170471731)
          ·
            refine ⟨63224132595489204255707597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42149421730326136170471731 63224132595489204255707597)
            ·
              refine ⟨23709049723308451595890349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63224132595489204255707597 23709049723308451595890349)
              ·
                refine ⟨8890893646240669348458881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23709049723308451595890349 8890893646240669348458881)
                ·
                  refine ⟨6668170234680502011344161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890893646240669348458881 6668170234680502011344161)
                  ·
                    refine ⟨5001127676010376508508121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668170234680502011344161 5001127676010376508508121)
                    ·
                      refine ⟨3750845757007782381381091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001127676010376508508121 3750845757007782381381091)
                      ·
                        rfl

theorem cell23_7304746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7304746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304746 prefixEnd_7304746 := by exact prefixLift 7304746
  have htrace : WordTrace (prefixWord ++ tailWord_7304746) baseStart_7304746 baseEnd_7304746 := by
    simpa [prefixWord, tailWord_7304746, baseEnd_7304746] using wordTrace_append hprefix tailTrace_7304746
  have hstable : (prefixWord ++ tailWord_7304746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304746).length < 2 ^ (prefixWord ++ tailWord_7304746).sum := by decide
  have hdescent : baseEnd_7304746 < baseStart_7304746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304786 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_7304786 : Nat := 118140960795 + 7304786 * 2 ^ 59
def prefixEnd_7304786 : Nat := 4983230072969 + 3 ^ 40 * 7304786 * 2
def baseEnd_7304786 : Nat := 416762921803773580542323

theorem tailTrace_7304786 : CollatzResearch.WordTrace tailWord_7304786 prefixEnd_7304786 416762921803773580542323 := by
  unfold tailWord_7304786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66606858328503838742683553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177618288876010236647156141 66606858328503838742683553)
  ·
    refine ⟨49955143746377879057012665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66606858328503838742683553 49955143746377879057012665)
    ·
      refine ⟨37466357809783409292759499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49955143746377879057012665 37466357809783409292759499)
      ·
        refine ⟨56199536714675113939139249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37466357809783409292759499 56199536714675113939139249)
        ·
          refine ⟨42149652536006335454354437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56199536714675113939139249 42149652536006335454354437)
          ·
            refine ⟨7903059850501187897691457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42149652536006335454354437 7903059850501187897691457)
            ·
              refine ⟨5927294887875890923268593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7903059850501187897691457 5927294887875890923268593)
              ·
                refine ⟨4445471165906918192451445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5927294887875890923268593 4445471165906918192451445)
                ·
                  refine ⟨416762921803773580542323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4445471165906918192451445 416762921803773580542323)
                  ·
                    rfl

theorem cell23_7304786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_7304786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304786 prefixEnd_7304786 := by exact prefixLift 7304786
  have htrace : WordTrace (prefixWord ++ tailWord_7304786) baseStart_7304786 baseEnd_7304786 := by
    simpa [prefixWord, tailWord_7304786, baseEnd_7304786] using wordTrace_append hprefix tailTrace_7304786
  have hstable : (prefixWord ++ tailWord_7304786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304786).length < 2 ^ (prefixWord ++ tailWord_7304786).sum := by decide
  have hdescent : baseEnd_7304786 < baseStart_7304786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304825 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 8]
def baseStart_7304825 : Nat := 118140960795 + 7304825 * 2 ^ 59
def prefixEnd_7304825 : Nat := 4983230072969 + 3 ^ 40 * 7304825 * 2
def baseEnd_7304825 : Nat := 416765146886609730254803

theorem tailTrace_7304825 : CollatzResearch.WordTrace tailWord_7304825 prefixEnd_7304825 416765146886609730254803 := by
  unfold tailWord_7304825
  simp only [CollatzResearch.WordTrace]
  refine ⟨266428855760874064631403929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177619237173916043087602619 266428855760874064631403929)
  ·
    refine ⟨199821641820655548473552947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266428855760874064631403929 199821641820655548473552947)
    ·
      refine ⟨299732462730983322710329421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199821641820655548473552947 299732462730983322710329421)
      ·
        refine ⟨112399673524118746016373533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299732462730983322710329421 112399673524118746016373533)
        ·
          refine ⟨42149877571544529756140075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112399673524118746016373533 42149877571544529756140075)
          ·
            refine ⟨63224816357316794634210113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42149877571544529756140075 63224816357316794634210113)
            ·
              refine ⟨47418612267987595975657585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63224816357316794634210113 47418612267987595975657585)
              ·
                refine ⟨35563959200990696981743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47418612267987595975657585 35563959200990696981743189)
                ·
                  refine ⟨416765146886609730254803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35563959200990696981743189 416765146886609730254803)
                  ·
                    rfl

theorem cell23_7304825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_7304825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304825 prefixEnd_7304825 := by exact prefixLift 7304825
  have htrace : WordTrace (prefixWord ++ tailWord_7304825) baseStart_7304825 baseEnd_7304825 := by
    simpa [prefixWord, tailWord_7304825, baseEnd_7304825] using wordTrace_append hprefix tailTrace_7304825
  have hstable : (prefixWord ++ tailWord_7304825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304825).length < 2 ^ (prefixWord ++ tailWord_7304825).sum := by decide
  have hdescent : baseEnd_7304825 < baseStart_7304825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304842 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_7304842 : Nat := 118140960795 + 7304842 * 2 ^ 59
def prefixEnd_7304842 : Nat := 4983230072969 + 3 ^ 40 * 7304842 * 2
def baseEnd_7304842 : Nat := 416766116794512667308961

theorem tailTrace_7304842 : CollatzResearch.WordTrace tailWord_7304842 prefixEnd_7304842 416766116794512667308961 := by
  unfold tailWord_7304842
  simp only [CollatzResearch.WordTrace]
  refine ⟨66607368950453119133693195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177619650534541651023181853 66607368950453119133693195)
  ·
    refine ⟨99911053425679678700539793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66607368950453119133693195 99911053425679678700539793)
    ·
      refine ⟨74933290069259759025404845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99911053425679678700539793 74933290069259759025404845)
      ·
        refine ⟨28099983775972409634526817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74933290069259759025404845 28099983775972409634526817)
        ·
          refine ⟨21074987831979307225895113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28099983775972409634526817 21074987831979307225895113)
          ·
            refine ⟨15806240873984480419421335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21074987831979307225895113 15806240873984480419421335)
            ·
              refine ⟨23709361310976720629132003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15806240873984480419421335 23709361310976720629132003)
              ·
                refine ⟨35564041966465080943698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23709361310976720629132003 35564041966465080943698005)
                ·
                  refine ⟨416766116794512667308961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35564041966465080943698005 416766116794512667308961)
                  ·
                    rfl

theorem cell23_7304842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_7304842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304842 prefixEnd_7304842 := by exact prefixLift 7304842
  have htrace : WordTrace (prefixWord ++ tailWord_7304842) baseStart_7304842 baseEnd_7304842 := by
    simpa [prefixWord, tailWord_7304842, baseEnd_7304842] using wordTrace_append hprefix tailTrace_7304842
  have hstable : (prefixWord ++ tailWord_7304842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304842).length < 2 ^ (prefixWord ++ tailWord_7304842).sum := by decide
  have hdescent : baseEnd_7304842 < baseStart_7304842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304846 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_7304846 : Nat := 118140960795 + 7304846 * 2 ^ 59
def prefixEnd_7304846 : Nat := 4983230072969 + 3 ^ 40 * 7304846 * 2
def baseEnd_7304846 : Nat := 1250299035024410663376877

theorem tailTrace_7304846 : CollatzResearch.WordTrace tailWord_7304846 prefixEnd_7304846 1250299035024410663376877 := by
  unfold tailWord_7304846
  simp only [CollatzResearch.WordTrace]
  refine ⟨33303702711724748152239799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177619747795865323478612261 33303702711724748152239799)
  ·
    refine ⟨49955554067587122228359699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33303702711724748152239799 49955554067587122228359699)
    ·
      refine ⟨74933331101380683342539549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49955554067587122228359699 74933331101380683342539549)
      ·
        refine ⟨28099999163017756253452331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74933331101380683342539549 28099999163017756253452331)
        ·
          refine ⟨42149998744526634380178497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28099999163017756253452331 42149998744526634380178497)
          ·
            refine ⟨31612499058394975785133873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42149998744526634380178497 31612499058394975785133873)
            ·
              refine ⟨23709374293796231838850405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31612499058394975785133873 23709374293796231838850405)
              ·
                refine ⟨4445507680086793469784451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23709374293796231838850405 4445507680086793469784451)
                ·
                  refine ⟨6668261520130190204676677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445507680086793469784451 6668261520130190204676677)
                  ·
                    refine ⟨1250299035024410663376877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668261520130190204676677 1250299035024410663376877)
                    ·
                      rfl

theorem cell23_7304846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_7304846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304846 prefixEnd_7304846 := by exact prefixLift 7304846
  have htrace : WordTrace (prefixWord ++ tailWord_7304846) baseStart_7304846 baseEnd_7304846 := by
    simpa [prefixWord, tailWord_7304846, baseEnd_7304846] using wordTrace_append hprefix tailTrace_7304846
  have hstable : (prefixWord ++ tailWord_7304846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304846).length < 2 ^ (prefixWord ++ tailWord_7304846).sum := by decide
  have hdescent : baseEnd_7304846 < baseStart_7304846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304869 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_7304869 : Nat := 118140960795 + 7304869 * 2 ^ 59
def prefixEnd_7304869 : Nat := 4983230072969 + 3 ^ 40 * 7304869 * 2
def baseEnd_7304869 : Nat := 3750908915128285400143025

theorem tailTrace_7304869 : CollatzResearch.WordTrace tailWord_7304869 prefixEnd_7304869 3750908915128285400143025 := by
  unfold tailWord_7304869
  simp only [CollatzResearch.WordTrace]
  refine ⟨266430460572714660146005661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177620307048476440097337107 266430460572714660146005661)
  ·
    refine ⟨99911422714767997554752123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266430460572714660146005661 99911422714767997554752123)
    ·
      refine ⟨149867134072151996332128185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99911422714767997554752123 149867134072151996332128185)
      ·
        refine ⟨112400350554113997249096139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149867134072151996332128185 112400350554113997249096139)
        ·
          refine ⟨168600525831170995873644209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112400350554113997249096139 168600525831170995873644209)
          ·
            refine ⟨126450394373378246905233157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168600525831170995873644209 126450394373378246905233157)
            ·
              refine ⟨23709448945008421294731217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126450394373378246905233157 23709448945008421294731217)
              ·
                refine ⟨17782086708756315971048413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23709448945008421294731217 17782086708756315971048413)
                ·
                  refine ⟨6668282515783618489143155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17782086708756315971048413 6668282515783618489143155)
                  ·
                    refine ⟨10002423773675427733714733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668282515783618489143155 10002423773675427733714733)
                    ·
                      refine ⟨3750908915128285400143025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10002423773675427733714733 3750908915128285400143025)
                      ·
                        rfl

theorem cell23_7304869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_7304869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304869 prefixEnd_7304869 := by exact prefixLift 7304869
  have htrace : WordTrace (prefixWord ++ tailWord_7304869) baseStart_7304869 baseEnd_7304869 := by
    simpa [prefixWord, tailWord_7304869, baseEnd_7304869] using wordTrace_append hprefix tailTrace_7304869
  have hstable : (prefixWord ++ tailWord_7304869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304869).length < 2 ^ (prefixWord ++ tailWord_7304869).sum := by decide
  have hdescent : baseEnd_7304869 < baseStart_7304869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304879 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 2, 3, 2]
def baseStart_7304879 : Nat := 118140960795 + 7304879 * 2 ^ 59
def prefixEnd_7304879 : Nat := 4983230072969 + 3 ^ 40 * 7304879 * 2
def baseEnd_7304879 : Nat := 3750914049934830361017979

theorem tailTrace_7304879 : CollatzResearch.WordTrace tailWord_7304879 prefixEnd_7304879 3750914049934830361017979 := by
  unfold tailWord_7304879
  simp only [CollatzResearch.WordTrace]
  refine ⟨266430825302678431853869691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177620550201785621235913127 266430825302678431853869691)
  ·
    refine ⟨399646237954017647780804537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266430825302678431853869691 399646237954017647780804537)
    ·
      refine ⟨299734678465513235835603403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399646237954017647780804537 299734678465513235835603403)
      ·
        refine ⟨449602017698269853753405105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299734678465513235835603403 449602017698269853753405105)
        ·
          refine ⟨337201513273702390315053829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449602017698269853753405105 337201513273702390315053829)
          ·
            refine ⟨63225283738819198184072593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337201513273702390315053829 63225283738819198184072593)
            ·
              refine ⟨47418962804114398638054445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63225283738819198184072593 47418962804114398638054445)
              ·
                refine ⟨17782111051542899489270417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47418962804114398638054445 17782111051542899489270417)
                ·
                  refine ⟨13336583288657174616952813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17782111051542899489270417 13336583288657174616952813)
                  ·
                    refine ⟨5001218733246440481357305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13336583288657174616952813 5001218733246440481357305)
                    ·
                      refine ⟨3750914049934830361017979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001218733246440481357305 3750914049934830361017979)
                      ·
                        rfl

theorem cell23_7304879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3, 2].length) (baseStart_7304879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304879 prefixEnd_7304879 := by exact prefixLift 7304879
  have htrace : WordTrace (prefixWord ++ tailWord_7304879) baseStart_7304879 baseEnd_7304879 := by
    simpa [prefixWord, tailWord_7304879, baseEnd_7304879] using wordTrace_append hprefix tailTrace_7304879
  have hstable : (prefixWord ++ tailWord_7304879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304879).length < 2 ^ (prefixWord ++ tailWord_7304879).sum := by decide
  have hdescent : baseEnd_7304879 < baseStart_7304879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304903 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_7304903 : Nat := 118140960795 + 7304903 * 2 ^ 59
def prefixEnd_7304903 : Nat := 4983230072969 + 3 ^ 40 * 7304903 * 2
def baseEnd_7304903 : Nat := 3750926373470538267117869

theorem tailTrace_7304903 : CollatzResearch.WordTrace tailWord_7304903 prefixEnd_7304903 3750926373470538267117869 := by
  unfold tailWord_7304903
  simp only [CollatzResearch.WordTrace]
  refine ⟨266431700654591483952743363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177621133769727655968495575 266431700654591483952743363)
  ·
    refine ⟨399647550981887225929115045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266431700654591483952743363 399647550981887225929115045)
    ·
      refine ⟨74933915809103854861709071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399647550981887225929115045 74933915809103854861709071)
      ·
        refine ⟨112400873713655782292563607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74933915809103854861709071 112400873713655782292563607)
        ·
          refine ⟨168601310570483673438845411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112400873713655782292563607 168601310570483673438845411)
          ·
            refine ⟨252901965855725510158268117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168601310570483673438845411 252901965855725510158268117)
            ·
              refine ⟨5927389824743566644334409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252901965855725510158268117 5927389824743566644334409)
              ·
                refine ⟨4445542368557674983250807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5927389824743566644334409 4445542368557674983250807)
                ·
                  refine ⟨6668313552836512474876211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445542368557674983250807 6668313552836512474876211)
                  ·
                    refine ⟨10002470329254768712314317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668313552836512474876211 10002470329254768712314317)
                    ·
                      refine ⟨3750926373470538267117869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10002470329254768712314317 3750926373470538267117869)
                      ·
                        rfl

theorem cell23_7304903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_7304903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304903 prefixEnd_7304903 := by exact prefixLift 7304903
  have htrace : WordTrace (prefixWord ++ tailWord_7304903) baseStart_7304903 baseEnd_7304903 := by
    simpa [prefixWord, tailWord_7304903, baseEnd_7304903] using wordTrace_append hprefix tailTrace_7304903
  have hstable : (prefixWord ++ tailWord_7304903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304903).length < 2 ^ (prefixWord ++ tailWord_7304903).sum := by decide
  have hdescent : baseEnd_7304903 < baseStart_7304903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304919 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 2, 4]
def baseStart_7304919 : Nat := 118140960795 + 7304919 * 2 ^ 59
def prefixEnd_7304919 : Nat := 4983230072969 + 3 ^ 40 * 7304919 * 2
def baseEnd_7304919 : Nat := 1250311529720336734839265

theorem tailTrace_7304919 : CollatzResearch.WordTrace tailWord_7304919 prefixEnd_7304919 1250311529720336734839265 := by
  unfold tailWord_7304919
  simp only [CollatzResearch.WordTrace]
  refine ⟨266432284222533518685325811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177621522815022345790217207 266432284222533518685325811)
  ·
    refine ⟨399648426333800278027988717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266432284222533518685325811 399648426333800278027988717)
    ·
      refine ⟨149868159875175104260495769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399648426333800278027988717 149868159875175104260495769)
      ·
        refine ⟨112401119906381328195371827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149868159875175104260495769 112401119906381328195371827)
        ·
          refine ⟨168601679859571992293057741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112401119906381328195371827 168601679859571992293057741)
          ·
            refine ⟨63225629947339497109896653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168601679859571992293057741 63225629947339497109896653)
            ·
              refine ⟨23709611230252311416211245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63225629947339497109896653 23709611230252311416211245)
              ·
                refine ⟨8891104211344616781079217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23709611230252311416211245 8891104211344616781079217)
                ·
                  refine ⟨6668328158508462585809413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8891104211344616781079217 6668328158508462585809413)
                  ·
                    refine ⟨1250311529720336734839265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668328158508462585809413 1250311529720336734839265)
                    ·
                      rfl

theorem cell23_7304919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_7304919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304919 prefixEnd_7304919 := by exact prefixLift 7304919
  have htrace : WordTrace (prefixWord ++ tailWord_7304919) baseStart_7304919 baseEnd_7304919 := by
    simpa [prefixWord, tailWord_7304919, baseEnd_7304919] using wordTrace_append hprefix tailTrace_7304919
  have hstable : (prefixWord ++ tailWord_7304919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304919).length < 2 ^ (prefixWord ++ tailWord_7304919).sum := by decide
  have hdescent : baseEnd_7304919 < baseStart_7304919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304922 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_7304922 : Nat := 118140960795 + 7304922 * 2 ^ 59
def prefixEnd_7304922 : Nat := 4983230072969 + 3 ^ 40 * 7304922 * 2
def baseEnd_7304922 : Nat := 3750936129602973692780281

theorem tailTrace_7304922 : CollatzResearch.WordTrace tailWord_7304922 prefixEnd_7304922 3750936129602973692780281 := by
  unfold tailWord_7304922
  simp only [CollatzResearch.WordTrace]
  refine ⟨66608098410380662549421255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177621595761015100131790013 66608098410380662549421255)
  ·
    refine ⟨99912147615570993824131883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66608098410380662549421255 99912147615570993824131883)
    ·
      refine ⟨149868221423356490736197825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99912147615570993824131883 149868221423356490736197825)
      ·
        refine ⟨112401166067517368052148369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149868221423356490736197825 112401166067517368052148369)
        ·
          refine ⟨84300874550638026039111277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112401166067517368052148369 84300874550638026039111277)
          ·
            refine ⟨31612827956489259764666729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84300874550638026039111277 31612827956489259764666729)
            ·
              refine ⟨23709620967366944823500047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31612827956489259764666729 23709620967366944823500047)
              ·
                refine ⟨35564431451050417235250071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23709620967366944823500047 35564431451050417235250071)
                ·
                  refine ⟨53346647176575625852875107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35564431451050417235250071 53346647176575625852875107)
                  ·
                    refine ⟨80019970764863438779312661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53346647176575625852875107 80019970764863438779312661)
                    ·
                      refine ⟨3750936129602973692780281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80019970764863438779312661 3750936129602973692780281)
                      ·
                        rfl

theorem cell23_7304922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_7304922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304922 prefixEnd_7304922 := by exact prefixLift 7304922
  have htrace : WordTrace (prefixWord ++ tailWord_7304922) baseStart_7304922 baseEnd_7304922 := by
    simpa [prefixWord, tailWord_7304922, baseEnd_7304922] using wordTrace_append hprefix tailTrace_7304922
  have hstable : (prefixWord ++ tailWord_7304922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304922).length < 2 ^ (prefixWord ++ tailWord_7304922).sum := by decide
  have hdescent : baseEnd_7304922 < baseStart_7304922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304943 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 1, 2, 2]
def baseStart_7304943 : Nat := 118140960795 + 7304943 * 2 ^ 59
def prefixEnd_7304943 : Nat := 4983230072969 + 3 ^ 40 * 7304943 * 2
def baseEnd_7304943 : Nat := 3750946912696718110617685

theorem tailTrace_7304943 : CollatzResearch.WordTrace tailWord_7304943 prefixEnd_7304943 3750946912696718110617685 := by
  unfold tailWord_7304943
  simp only [CollatzResearch.WordTrace]
  refine ⟨266433159574446570784199483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177622106382964380522799655 266433159574446570784199483)
  ·
    refine ⟨399649739361669856176299225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266433159574446570784199483 399649739361669856176299225)
    ·
      refine ⟨299737304521252392132224419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399649739361669856176299225 299737304521252392132224419)
      ·
        refine ⟨449605956781878588198336629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299737304521252392132224419 449605956781878588198336629)
        ·
          refine ⟨42150558448301117643594059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 449605956781878588198336629 42150558448301117643594059)
          ·
            refine ⟨63225837672451676465391089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42150558448301117643594059 63225837672451676465391089)
            ·
              refine ⟨47419378254338757349043317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63225837672451676465391089 47419378254338757349043317)
              ·
                refine ⟨4445566711344258501472811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47419378254338757349043317 4445566711344258501472811)
                ·
                  refine ⟨6668350067016387752209217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445566711344258501472811 6668350067016387752209217)
                  ·
                    refine ⟨5001262550262290814156913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668350067016387752209217 5001262550262290814156913)
                    ·
                      refine ⟨3750946912696718110617685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001262550262290814156913 3750946912696718110617685)
                      ·
                        rfl

theorem cell23_7304943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 2, 2].length) (baseStart_7304943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304943 prefixEnd_7304943 := by exact prefixLift 7304943
  have htrace : WordTrace (prefixWord ++ tailWord_7304943) baseStart_7304943 baseEnd_7304943 := by
    simpa [prefixWord, tailWord_7304943, baseEnd_7304943] using wordTrace_append hprefix tailTrace_7304943
  have hstable : (prefixWord ++ tailWord_7304943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304943).length < 2 ^ (prefixWord ++ tailWord_7304943).sum := by decide
  have hdescent : baseEnd_7304943 < baseStart_7304943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304959 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 3]
def baseStart_7304959 : Nat := 118140960795 + 7304959 * 2 ^ 59
def prefixEnd_7304959 : Nat := 4983230072969 + 3 ^ 40 * 7304959 * 2
def baseEnd_7304959 : Nat := 3750955128387190048017611

theorem tailTrace_7304959 : CollatzResearch.WordTrace tailWord_7304959 prefixEnd_7304959 3750955128387190048017611 := by
  unfold tailWord_7304959
  simp only [CollatzResearch.WordTrace]
  refine ⟨266433743142388605516781931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177622495428259070344521287 266433743142388605516781931)
  ·
    refine ⟨399650614713582908275172897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266433743142388605516781931 399650614713582908275172897)
    ·
      refine ⟨299737961035187181206379673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399650614713582908275172897 299737961035187181206379673)
      ·
        refine ⟨224803470776390385904784755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299737961035187181206379673 224803470776390385904784755)
        ·
          refine ⟨337205206164585578857177133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224803470776390385904784755 337205206164585578857177133)
          ·
            refine ⟨126451952311719592071441425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337205206164585578857177133 126451952311719592071441425)
            ·
              refine ⟨94838964233789694053581069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126451952311719592071441425 94838964233789694053581069)
              ·
                refine ⟨35564611587671135270092901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94838964233789694053581069 35564611587671135270092901)
                ·
                  refine ⟨6668364672688337863142419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35564611587671135270092901 6668364672688337863142419)
                  ·
                    refine ⟨10002547009032506794713629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668364672688337863142419 10002547009032506794713629)
                    ·
                      refine ⟨3750955128387190048017611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10002547009032506794713629 3750955128387190048017611)
                      ·
                        rfl

theorem cell23_7304959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_7304959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304959 prefixEnd_7304959 := by exact prefixLift 7304959
  have htrace : WordTrace (prefixWord ++ tailWord_7304959) baseStart_7304959 baseEnd_7304959 := by
    simpa [prefixWord, tailWord_7304959, baseEnd_7304959] using wordTrace_append hprefix tailTrace_7304959
  have hstable : (prefixWord ++ tailWord_7304959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304959).length < 2 ^ (prefixWord ++ tailWord_7304959).sum := by decide
  have hdescent : baseEnd_7304959 < baseStart_7304959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304986 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_7304986 : Nat := 118140960795 + 7304986 * 2 ^ 59
def prefixEnd_7304986 : Nat := 4983230072969 + 3 ^ 40 * 7304986 * 2
def baseEnd_7304986 : Nat := 3750968992364861442379987

theorem tailTrace_7304986 : CollatzResearch.WordTrace tailWord_7304986 prefixEnd_7304986 3750968992364861442379987 := by
  unfold tailWord_7304986
  simp only [CollatzResearch.WordTrace]
  refine ⟨66608681978322697282003703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177623151942193859418676541 66608681978322697282003703)
  ·
    refine ⟨99913022967484045923005555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66608681978322697282003703 99913022967484045923005555)
    ·
      refine ⟨149869534451226068884508333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99913022967484045923005555 149869534451226068884508333)
      ·
        refine ⟨56201075419209775831690625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149869534451226068884508333 56201075419209775831690625)
        ·
          refine ⟨42150806564407331873767969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56201075419209775831690625 42150806564407331873767969)
          ·
            refine ⟨31613104923305498905325977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42150806564407331873767969 31613104923305498905325977)
            ·
              refine ⟨23709828692479124178994483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31613104923305498905325977 23709828692479124178994483)
              ·
                refine ⟨35564743038718686268491725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23709828692479124178994483 35564743038718686268491725)
                ·
                  refine ⟨13336778639519507350684397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35564743038718686268491725 13336778639519507350684397)
                  ·
                    refine ⟨5001291989819815256506649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13336778639519507350684397 5001291989819815256506649)
                    ·
                      refine ⟨3750968992364861442379987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001291989819815256506649 3750968992364861442379987)
                      ·
                        rfl

theorem cell23_7304986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_7304986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304986 prefixEnd_7304986 := by exact prefixLift 7304986
  have htrace : WordTrace (prefixWord ++ tailWord_7304986) baseStart_7304986 baseEnd_7304986 := by
    simpa [prefixWord, tailWord_7304986, baseEnd_7304986] using wordTrace_append hprefix tailTrace_7304986
  have hstable : (prefixWord ++ tailWord_7304986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304986).length < 2 ^ (prefixWord ++ tailWord_7304986).sum := by decide
  have hdescent : baseEnd_7304986 < baseStart_7304986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7304992 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_7304992 : Nat := 118140960795 + 7304992 * 2 ^ 59
def prefixEnd_7304992 : Nat := 4983230072969 + 3 ^ 40 * 7304992 * 2
def baseEnd_7304992 : Nat := 1250324024416262806301653

theorem tailTrace_7304992 : CollatzResearch.WordTrace tailWord_7304992 prefixEnd_7304992 1250324024416262806301653 := by
  unfold tailWord_7304992
  simp only [CollatzResearch.WordTrace]
  refine ⟨133217473375634526076366615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177623297834179368101822153 133217473375634526076366615)
  ·
    refine ⟨199826210063451789114549923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133217473375634526076366615 199826210063451789114549923)
    ·
      refine ⟨299739315095177683671824885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199826210063451789114549923 299739315095177683671824885)
      ·
        refine ⟨28100560790172907844233583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299739315095177683671824885 28100560790172907844233583)
        ·
          refine ⟨42150841185259361766350375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28100560790172907844233583 42150841185259361766350375)
          ·
            refine ⟨63226261777889042649525563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42150841185259361766350375 63226261777889042649525563)
            ·
              refine ⟨94839392666833563974288345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63226261777889042649525563 94839392666833563974288345)
              ·
                refine ⟨71129544500125172980716259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94839392666833563974288345 71129544500125172980716259)
                ·
                  refine ⟨106694316750187759471074389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71129544500125172980716259 106694316750187759471074389)
                  ·
                    refine ⟨1250324024416262806301653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106694316750187759471074389 1250324024416262806301653)
                    ·
                      rfl

theorem cell23_7304992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_7304992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7304992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7304992 prefixEnd_7304992 := by exact prefixLift 7304992
  have htrace : WordTrace (prefixWord ++ tailWord_7304992) baseStart_7304992 baseEnd_7304992 := by
    simpa [prefixWord, tailWord_7304992, baseEnd_7304992] using wordTrace_append hprefix tailTrace_7304992
  have hstable : (prefixWord ++ tailWord_7304992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7304992).length < 2 ^ (prefixWord ++ tailWord_7304992).sum := by decide
  have hdescent : baseEnd_7304992 < baseStart_7304992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7304992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305056 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 5]
def baseStart_7305056 : Nat := 118140960795 + 7305056 * 2 ^ 59
def prefixEnd_7305056 : Nat := 4983230072969 + 3 ^ 40 * 7305056 * 2
def baseEnd_7305056 : Nat := 416778326223408463167185

theorem tailTrace_7305056 : CollatzResearch.WordTrace tailWord_7305056 prefixEnd_7305056 416778326223408463167185 := by
  unfold tailWord_7305056
  simp only [CollatzResearch.WordTrace]
  refine ⟨133218640511518595541531511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177624854015358127388708681 133218640511518595541531511)
  ·
    refine ⟨199827960767277893312297267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133218640511518595541531511 199827960767277893312297267)
    ·
      refine ⟨299741941150916839968445901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199827960767277893312297267 299741941150916839968445901)
      ·
        refine ⟨112403227931593814988167213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299741941150916839968445901 112403227931593814988167213)
        ·
          refine ⟨42151210474347680620562705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112403227931593814988167213 42151210474347680620562705)
          ·
            refine ⟨31613407855760760465422029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42151210474347680620562705 31613407855760760465422029)
            ·
              refine ⟨11855027945910285174533261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31613407855760760465422029 11855027945910285174533261)
              ·
                refine ⟨4445635479716356940449973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855027945910285174533261 4445635479716356940449973)
                ·
                  refine ⟨416778326223408463167185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4445635479716356940449973 416778326223408463167185)
                  ·
                    rfl

theorem cell23_7305056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 5].length) (baseStart_7305056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305056 prefixEnd_7305056 := by exact prefixLift 7305056
  have htrace : WordTrace (prefixWord ++ tailWord_7305056) baseStart_7305056 baseEnd_7305056 := by
    simpa [prefixWord, tailWord_7305056, baseEnd_7305056] using wordTrace_append hprefix tailTrace_7305056
  have hstable : (prefixWord ++ tailWord_7305056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305056).length < 2 ^ (prefixWord ++ tailWord_7305056).sum := by decide
  have hdescent : baseEnd_7305056 < baseStart_7305056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305069 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_7305069 : Nat := 118140960795 + 7305069 * 2 ^ 59
def prefixEnd_7305069 : Nat := 4983230072969 + 3 ^ 40 * 7305069 * 2
def baseEnd_7305069 : Nat := 1250337203753061539214035

theorem tailTrace_7305069 : CollatzResearch.WordTrace tailWord_7305069 prefixEnd_7305069 1250337203753061539214035 := by
  unfold tailWord_7305069
  simp only [CollatzResearch.WordTrace]
  refine ⟨266437755171990094303286261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177625170114660062868857507 266437755171990094303286261)
  ·
    refine ⟨24978539547374071340933087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266437755171990094303286261 24978539547374071340933087)
    ·
      refine ⟨37467809321061107011399631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24978539547374071340933087 37467809321061107011399631)
      ·
        refine ⟨56201713981591660517099447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37467809321061107011399631 56201713981591660517099447)
        ·
          refine ⟨84302570972387490775649171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56201713981591660517099447 84302570972387490775649171)
          ·
            refine ⟨126453856458581236163473757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84302570972387490775649171 126453856458581236163473757)
            ·
              refine ⟨47420196171967963561302659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126453856458581236163473757 47420196171967963561302659)
              ·
                refine ⟨71130294257951945341953989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47420196171967963561302659 71130294257951945341953989)
                ·
                  refine ⟨13336930173365989751616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71130294257951945341953989 13336930173365989751616373)
                  ·
                    refine ⟨1250337203753061539214035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13336930173365989751616373 1250337203753061539214035)
                    ·
                      rfl

theorem cell23_7305069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_7305069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305069 prefixEnd_7305069 := by exact prefixLift 7305069
  have htrace : WordTrace (prefixWord ++ tailWord_7305069) baseStart_7305069 baseEnd_7305069 := by
    simpa [prefixWord, tailWord_7305069, baseEnd_7305069] using wordTrace_append hprefix tailTrace_7305069
  have hstable : (prefixWord ++ tailWord_7305069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305069).length < 2 ^ (prefixWord ++ tailWord_7305069).sum := by decide
  have hdescent : baseEnd_7305069 < baseStart_7305069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305099 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 5, 4]
def baseStart_7305099 : Nat := 118140960795 + 7305099 * 2 ^ 59
def prefixEnd_7305099 : Nat := 4983230072969 + 3 ^ 40 * 7305099 * 2
def baseEnd_7305099 : Nat := 1250342338559606500088989

theorem tailTrace_7305099 : CollatzResearch.WordTrace tailWord_7305099 prefixEnd_7305099 1250342338559606500088989 := by
  unfold tailWord_7305099
  simp only [CollatzResearch.WordTrace]
  refine ⟨266438849361881409426878351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177625899574587606284585567 266438849361881409426878351)
  ·
    refine ⟨399658274042822114140317527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266438849361881409426878351 399658274042822114140317527)
    ·
      refine ⟨599487411064233171210476291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399658274042822114140317527 599487411064233171210476291)
      ·
        refine ⟨899231116596349756815714437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599487411064233171210476291 899231116596349756815714437)
        ·
          refine ⟨168605834361815579402946457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 899231116596349756815714437 168605834361815579402946457)
          ·
            refine ⟨126454375771361684552209843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168605834361815579402946457 126454375771361684552209843)
            ·
              refine ⟨189681563657042526828314765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126454375771361684552209843 189681563657042526828314765)
              ·
                refine ⟨71130586371390947560618037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189681563657042526828314765 71130586371390947560618037)
                ·
                  refine ⟨6668492472317901333807941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71130586371390947560618037 6668492472317901333807941)
                  ·
                    refine ⟨1250342338559606500088989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668492472317901333807941 1250342338559606500088989)
                    ·
                      rfl

theorem cell23_7305099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 4].length) (baseStart_7305099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305099 prefixEnd_7305099 := by exact prefixLift 7305099
  have htrace : WordTrace (prefixWord ++ tailWord_7305099) baseStart_7305099 baseEnd_7305099 := by
    simpa [prefixWord, tailWord_7305099, baseEnd_7305099] using wordTrace_append hprefix tailTrace_7305099
  have hstable : (prefixWord ++ tailWord_7305099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305099).length < 2 ^ (prefixWord ++ tailWord_7305099).sum := by decide
  have hdescent : baseEnd_7305099 < baseStart_7305099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305176 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_7305176 : Nat := 118140960795 + 7305176 * 2 ^ 59
def prefixEnd_7305176 : Nat := 4983230072969 + 3 ^ 40 * 7305176 * 2
def baseEnd_7305176 : Nat := 1250355517896405233001371

theorem tailTrace_7305176 : CollatzResearch.WordTrace tailWord_7305176 prefixEnd_7305176 1250355517896405233001371 := by
  unfold tailWord_7305176
  simp only [CollatzResearch.WordTrace]
  refine ⟨133220828891301225788715691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177627771855068301051620921 133220828891301225788715691)
  ·
    refine ⟨199831243336951838683073537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133220828891301225788715691 199831243336951838683073537)
    ·
      refine ⟨149873432502713879012305153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199831243336951838683073537 149873432502713879012305153)
      ·
        refine ⟨112405074377035409259228865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149873432502713879012305153 112405074377035409259228865)
        ·
          refine ⟨84303805782776556944421649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112405074377035409259228865 84303805782776556944421649)
          ·
            refine ⟨63227854337082417708316237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84303805782776556944421649 63227854337082417708316237)
            ·
              refine ⟨23710445376405906640618589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63227854337082417708316237 23710445376405906640618589)
              ·
                refine ⟨8891417016152214990231971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23710445376405906640618589 8891417016152214990231971)
                ·
                  refine ⟨13337125524228322485347957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8891417016152214990231971 13337125524228322485347957)
                  ·
                    refine ⟨1250355517896405233001371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13337125524228322485347957 1250355517896405233001371)
                    ·
                      rfl

theorem cell23_7305176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_7305176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305176 prefixEnd_7305176 := by exact prefixLift 7305176
  have htrace : WordTrace (prefixWord ++ tailWord_7305176) baseStart_7305176 baseEnd_7305176 := by
    simpa [prefixWord, tailWord_7305176, baseEnd_7305176] using wordTrace_append hprefix tailTrace_7305176
  have hstable : (prefixWord ++ tailWord_7305176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305176).length < 2 ^ (prefixWord ++ tailWord_7305176).sum := by decide
  have hdescent : baseEnd_7305176 < baseStart_7305176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305180 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 8]
def baseStart_7305180 : Nat := 118140960795 + 7305180 * 2 ^ 59
def prefixEnd_7305180 : Nat := 4983230072969 + 3 ^ 40 * 7305180 * 2
def baseEnd_7305180 : Nat := 416785400845759298150455

theorem tailTrace_7305180 : CollatzResearch.WordTrace tailWord_7305180 prefixEnd_7305180 416785400845759298150455 := by
  unfold tailWord_7305180
  simp only [CollatzResearch.WordTrace]
  refine ⟨133220901837293980130288497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177627869116391973507051329 133220901837293980130288497)
  ·
    refine ⟨99915676377970485097716373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133220901837293980130288497 99915676377970485097716373)
    ·
      refine ⟨4683547330217366488955455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99915676377970485097716373 4683547330217366488955455)
      ·
        refine ⟨7025320995326049733433183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683547330217366488955455 7025320995326049733433183)
        ·
          refine ⟨10537981492989074600149775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025320995326049733433183 10537981492989074600149775)
          ·
            refine ⟨15806972239483611900224663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537981492989074600149775 15806972239483611900224663)
            ·
              refine ⟨23710458359225417850336995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15806972239483611900224663 23710458359225417850336995)
              ·
                refine ⟨35565687538838126775505493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23710458359225417850336995 35565687538838126775505493)
                ·
                  refine ⟨416785400845759298150455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35565687538838126775505493 416785400845759298150455)
                  ·
                    rfl

theorem cell23_7305180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_7305180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305180 prefixEnd_7305180 := by exact prefixLift 7305180
  have htrace : WordTrace (prefixWord ++ tailWord_7305180) baseStart_7305180 baseEnd_7305180 := by
    simpa [prefixWord, tailWord_7305180, baseEnd_7305180] using wordTrace_append hprefix tailTrace_7305180
  have hstable : (prefixWord ++ tailWord_7305180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305180).length < 2 ^ (prefixWord ++ tailWord_7305180).sum := by decide
  have hdescent : baseEnd_7305180 < baseStart_7305180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305259 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_7305259 : Nat := 118140960795 + 7305259 * 2 ^ 59
def prefixEnd_7305259 : Nat := 4983230072969 + 3 ^ 40 * 7305259 * 2
def baseEnd_7305259 : Nat := 3751109172583538874266231

theorem tailTrace_7305259 : CollatzResearch.WordTrace tailWord_7305259 prefixEnd_7305259 3751109172583538874266231 := by
  unfold tailWord_7305259
  simp only [CollatzResearch.WordTrace]
  refine ⟨266444685041301756752702831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177629790027534504501801887 266444685041301756752702831)
  ·
    refine ⟨399667027561952635129054247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266444685041301756752702831 399667027561952635129054247)
    ·
      refine ⟨599500541342928952693581371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399667027561952635129054247 599500541342928952693581371)
      ·
        refine ⟨899250812014393429040372057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599500541342928952693581371 899250812014393429040372057)
        ·
          refine ⟨674438109010795071780279043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899250812014393429040372057 674438109010795071780279043)
          ·
            refine ⟨1011657163516192607670418565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674438109010795071780279043 1011657163516192607670418565)
            ·
              refine ⟨189685718159286113938203481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1011657163516192607670418565 189685718159286113938203481)
              ·
                refine ⟨142264288619464585453652611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189685718159286113938203481 142264288619464585453652611)
                ·
                  refine ⟨213396432929196878180478917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142264288619464585453652611 213396432929196878180478917)
                  ·
                    refine ⟨40011831174224414658839797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213396432929196878180478917 40011831174224414658839797)
                    ·
                      refine ⟨3751109172583538874266231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40011831174224414658839797 3751109172583538874266231)
                      ·
                        rfl

theorem cell23_7305259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_7305259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305259 prefixEnd_7305259 := by exact prefixLift 7305259
  have htrace : WordTrace (prefixWord ++ tailWord_7305259) baseStart_7305259 baseEnd_7305259 := by
    simpa [prefixWord, tailWord_7305259, baseEnd_7305259] using wordTrace_append hprefix tailTrace_7305259
  have hstable : (prefixWord ++ tailWord_7305259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305259).length < 2 ^ (prefixWord ++ tailWord_7305259).sum := by decide
  have hdescent : baseEnd_7305259 < baseStart_7305259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305298 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_7305298 : Nat := 118140960795 + 7305298 * 2 ^ 59
def prefixEnd_7305298 : Nat := 4983230072969 + 3 ^ 40 * 7305298 * 2
def baseEnd_7305298 : Nat := 3751129198329064221678553

theorem tailTrace_7305298 : CollatzResearch.WordTrace tailWord_7305298 prefixEnd_7305298 3751129198329064221678553 := by
  unfold tailWord_7305298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611526872040116603343137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177630738325440310942248365 66611526872040116603343137)
  ·
    refine ⟨49958645154030087452507353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66611526872040116603343137 49958645154030087452507353)
    ·
      refine ⟨37468983865522565589380515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49958645154030087452507353 37468983865522565589380515)
      ·
        refine ⟨56203475798283848384070773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37468983865522565589380515 56203475798283848384070773)
        ·
          refine ⟨5269075856089110786006635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56203475798283848384070773 5269075856089110786006635)
          ·
            refine ⟨7903613784133666179009953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269075856089110786006635 7903613784133666179009953)
            ·
              refine ⟨5927710338100249634257465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7903613784133666179009953 5927710338100249634257465)
              ·
                refine ⟨4445782753575187225693099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5927710338100249634257465 4445782753575187225693099)
                ·
                  refine ⟨6668674130362780838539649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445782753575187225693099 6668674130362780838539649)
                  ·
                    refine ⟨5001505597772085628904737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668674130362780838539649 5001505597772085628904737)
                    ·
                      refine ⟨3751129198329064221678553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001505597772085628904737 3751129198329064221678553)
                      ·
                        rfl

theorem cell23_7305298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_7305298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305298 prefixEnd_7305298 := by exact prefixLift 7305298
  have htrace : WordTrace (prefixWord ++ tailWord_7305298) baseStart_7305298 baseEnd_7305298 := by
    simpa [prefixWord, tailWord_7305298, baseEnd_7305298] using wordTrace_append hprefix tailTrace_7305298
  have hstable : (prefixWord ++ tailWord_7305298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305298).length < 2 ^ (prefixWord ++ tailWord_7305298).sum := by decide
  have hdescent : baseEnd_7305298 < baseStart_7305298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305306 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_7305306 : Nat := 118140960795 + 7305306 * 2 ^ 59
def prefixEnd_7305306 : Nat := 4983230072969 + 3 ^ 40 * 7305306 * 2
def baseEnd_7305306 : Nat := 3751133306174300190378515

theorem tailTrace_7305306 : CollatzResearch.WordTrace tailWord_7305306 prefixEnd_7305306 3751133306174300190378515 := by
  unfold tailWord_7305306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611599818032870944915943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177630932848087655853109181 66611599818032870944915943)
  ·
    refine ⟨99917399727049306417373915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66611599818032870944915943 99917399727049306417373915)
    ·
      refine ⟨149876099590573959626060873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99917399727049306417373915 149876099590573959626060873)
      ·
        refine ⟨112407074692930469719545655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149876099590573959626060873 112407074692930469719545655)
        ·
          refine ⟨168610612039395704579318483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112407074692930469719545655 168610612039395704579318483)
          ·
            refine ⟨252915918059093556868977725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168610612039395704579318483 252915918059093556868977725)
            ·
              refine ⟨94843469272160083825866647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252915918059093556868977725 94843469272160083825866647)
              ·
                refine ⟨142265203908240125738799971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94843469272160083825866647 142265203908240125738799971)
                ·
                  refine ⟨213397805862360188608199957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142265203908240125738799971 213397805862360188608199957)
                  ·
                    refine ⟨10003022149798133841009373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213397805862360188608199957 10003022149798133841009373)
                    ·
                      refine ⟨3751133306174300190378515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003022149798133841009373 3751133306174300190378515)
                      ·
                        rfl

theorem cell23_7305306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_7305306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305306 prefixEnd_7305306 := by exact prefixLift 7305306
  have htrace : WordTrace (prefixWord ++ tailWord_7305306) baseStart_7305306 baseEnd_7305306 := by
    simpa [prefixWord, tailWord_7305306, baseEnd_7305306] using wordTrace_append hprefix tailTrace_7305306
  have hstable : (prefixWord ++ tailWord_7305306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305306).length < 2 ^ (prefixWord ++ tailWord_7305306).sum := by decide
  have hdescent : baseEnd_7305306 < baseStart_7305306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305316 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_7305316 : Nat := 118140960795 + 7305316 * 2 ^ 59
def prefixEnd_7305316 : Nat := 4983230072969 + 3 ^ 40 * 7305316 * 2
def baseEnd_7305316 : Nat := 3751138440980845151253469

theorem tailTrace_7305316 : CollatzResearch.WordTrace tailWord_7305316 prefixEnd_7305316 3751138440980845151253469 := by
  unfold tailWord_7305316
  simp only [CollatzResearch.WordTrace]
  refine ⟨133223382001047627743763901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177631176001396836991685201 133223382001047627743763901)
  ·
    refine ⟨49958768250392860403911463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133223382001047627743763901 49958768250392860403911463)
    ·
      refine ⟨74938152375589290605867195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49958768250392860403911463 74938152375589290605867195)
      ·
        refine ⟨112407228563383935908800793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74938152375589290605867195 112407228563383935908800793)
        ·
          refine ⟨84305421422537951931600595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112407228563383935908800793 84305421422537951931600595)
          ·
            refine ⟨126458132133806927897400893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84305421422537951931600595 126458132133806927897400893)
            ·
              refine ⟨47421799550177597961525335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126458132133806927897400893 47421799550177597961525335)
              ·
                refine ⟨71132699325266396942288003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47421799550177597961525335 71132699325266396942288003)
                ·
                  refine ⟨106699048987899595413432005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71132699325266396942288003 106699048987899595413432005)
                  ·
                    refine ⟨20006071685231174140018501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106699048987899595413432005 20006071685231174140018501)
                    ·
                      refine ⟨3751138440980845151253469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20006071685231174140018501 3751138440980845151253469)
                      ·
                        rfl

theorem cell23_7305316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_7305316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305316 prefixEnd_7305316 := by exact prefixLift 7305316
  have htrace : WordTrace (prefixWord ++ tailWord_7305316) baseStart_7305316 baseEnd_7305316 := by
    simpa [prefixWord, tailWord_7305316, baseEnd_7305316] using wordTrace_append hprefix tailTrace_7305316
  have hstable : (prefixWord ++ tailWord_7305316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305316).length < 2 ^ (prefixWord ++ tailWord_7305316).sum := by decide
  have hdescent : baseEnd_7305316 < baseStart_7305316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305336 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_7305336 : Nat := 118140960795 + 7305336 * 2 ^ 59
def prefixEnd_7305336 : Nat := 4983230072969 + 3 ^ 40 * 7305336 * 2
def baseEnd_7305336 : Nat := 3751148710593935073003377

theorem tailTrace_7305336 : CollatzResearch.WordTrace tailWord_7305336 prefixEnd_7305336 3751148710593935073003377 := by
  unfold tailWord_7305336
  simp only [CollatzResearch.WordTrace]
  refine ⟨133223746731011399451627931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177631662308015199268837241 133223746731011399451627931)
  ·
    refine ⟨199835620096517099177441897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133223746731011399451627931 199835620096517099177441897)
    ·
      refine ⟨149876715072387824383081423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199835620096517099177441897 149876715072387824383081423)
      ·
        refine ⟨224815072608581736574622135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149876715072387824383081423 224815072608581736574622135)
        ·
          refine ⟨337222608912872604861933203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224815072608581736574622135 337222608912872604861933203)
          ·
            refine ⟨505833913369308907292899805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337222608912872604861933203 505833913369308907292899805)
            ·
              refine ⟨189687717513490840234837427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505833913369308907292899805 189687717513490840234837427)
              ·
                refine ⟨284531576270236260352256141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189687717513490840234837427 284531576270236260352256141)
                ·
                  refine ⟨106699341101338597632096053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284531576270236260352256141 106699341101338597632096053)
                  ·
                    refine ⟨10003063228250493528009005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106699341101338597632096053 10003063228250493528009005)
                    ·
                      refine ⟨3751148710593935073003377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003063228250493528009005 3751148710593935073003377)
                      ·
                        rfl

theorem cell23_7305336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_7305336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305336 prefixEnd_7305336 := by exact prefixLift 7305336
  have htrace : WordTrace (prefixWord ++ tailWord_7305336) baseStart_7305336 baseEnd_7305336 := by
    simpa [prefixWord, tailWord_7305336, baseEnd_7305336] using wordTrace_append hprefix tailTrace_7305336
  have hstable : (prefixWord ++ tailWord_7305336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305336).length < 2 ^ (prefixWord ++ tailWord_7305336).sum := by decide
  have hdescent : baseEnd_7305336 < baseStart_7305336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305354 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_7305354 : Nat := 118140960795 + 7305354 * 2 ^ 59
def prefixEnd_7305354 : Nat := 4983230072969 + 3 ^ 40 * 7305354 * 2
def baseEnd_7305354 : Nat := 3751157953245716002578295

theorem tailTrace_7305354 : CollatzResearch.WordTrace tailWord_7305354 prefixEnd_7305354 3751157953245716002578295 := by
  unfold tailWord_7305354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66612037493989396994352779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177632099983971725318274077 66612037493989396994352779)
  ·
    refine ⟨99918056240984095491529169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66612037493989396994352779 99918056240984095491529169)
    ·
      refine ⟨74938542180738071618646877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99918056240984095491529169 74938542180738071618646877)
      ·
        refine ⟨28101953317776776856992579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74938542180738071618646877 28101953317776776856992579)
        ·
          refine ⟨42152929976665165285488869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28101953317776776856992579 42152929976665165285488869)
          ·
            refine ⟨7903674370624718491029163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42152929976665165285488869 7903674370624718491029163)
            ·
              refine ⟨11855511555937077736543745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903674370624718491029163 11855511555937077736543745)
              ·
                refine ⟨8891633666952808302407809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11855511555937077736543745 8891633666952808302407809)
                ·
                  refine ⟨6668725250214606226805857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8891633666952808302407809 6668725250214606226805857)
                  ·
                    refine ⟨5001543937660954670104393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668725250214606226805857 5001543937660954670104393)
                    ·
                      refine ⟨3751157953245716002578295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001543937660954670104393 3751157953245716002578295)
                      ·
                        rfl

theorem cell23_7305354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_7305354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305354 prefixEnd_7305354 := by exact prefixLift 7305354
  have htrace : WordTrace (prefixWord ++ tailWord_7305354) baseStart_7305354 baseEnd_7305354 := by
    simpa [prefixWord, tailWord_7305354, baseEnd_7305354] using wordTrace_append hprefix tailTrace_7305354
  have hstable : (prefixWord ++ tailWord_7305354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305354).length < 2 ^ (prefixWord ++ tailWord_7305354).sum := by decide
  have hdescent : baseEnd_7305354 < baseStart_7305354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305413 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_7305413 : Nat := 118140960795 + 7305413 * 2 ^ 59
def prefixEnd_7305413 : Nat := 4983230072969 + 3 ^ 40 * 7305413 * 2
def baseEnd_7305413 : Nat := 3751188248604331271740523

theorem tailTrace_7305413 : CollatzResearch.WordTrace tailWord_7305413 prefixEnd_7305413 3751188248604331271740523 := by
  unfold tailWord_7305413
  simp only [CollatzResearch.WordTrace]
  refine ⟨266450301882743841053808893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177633534588495894035872595 266450301882743841053808893)
  ·
    refine ⟨99918863206028940395178335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266450301882743841053808893 99918863206028940395178335)
    ·
      refine ⟨149878294809043410592767503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99918863206028940395178335 149878294809043410592767503)
      ·
        refine ⟨224817442213565115889151255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149878294809043410592767503 224817442213565115889151255)
        ·
          refine ⟨337226163320347673833726883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224817442213565115889151255 337226163320347673833726883)
          ·
            refine ⟨505839244980521510750590325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337226163320347673833726883 505839244980521510750590325)
            ·
              refine ⟨47422429216923891632867843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 505839244980521510750590325 47422429216923891632867843)
              ·
                refine ⟨71133643825385837449301765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47422429216923891632867843 71133643825385837449301765)
                ·
                  refine ⟨13337558217259844521744081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71133643825385837449301765 13337558217259844521744081)
                  ·
                    refine ⟨10003168662944883391308061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13337558217259844521744081 10003168662944883391308061)
                    ·
                      refine ⟨3751188248604331271740523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003168662944883391308061 3751188248604331271740523)
                      ·
                        rfl

theorem cell23_7305413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_7305413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305413 prefixEnd_7305413 := by exact prefixLift 7305413
  have htrace : WordTrace (prefixWord ++ tailWord_7305413) baseStart_7305413 baseEnd_7305413 := by
    simpa [prefixWord, tailWord_7305413, baseEnd_7305413] using wordTrace_append hprefix tailTrace_7305413
  have hstable : (prefixWord ++ tailWord_7305413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305413).length < 2 ^ (prefixWord ++ tailWord_7305413).sum := by decide
  have hdescent : baseEnd_7305413 < baseStart_7305413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305447 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7305447 : Nat := 118140960795 + 7305447 * 2 ^ 59
def prefixEnd_7305447 : Nat := 4983230072969 + 3 ^ 40 * 7305447 * 2
def baseEnd_7305447 : Nat := 3751205706946584138715367

theorem tailTrace_7305447 : CollatzResearch.WordTrace tailWord_7305447 prefixEnd_7305447 3751205706946584138715367 := by
  unfold tailWord_7305447
  simp only [CollatzResearch.WordTrace]
  refine ⟨266451541964620664860546595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177634361309747109907031063 266451541964620664860546595)
  ·
    refine ⟨399677312946930997290819893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266451541964620664860546595 399677312946930997290819893)
    ·
      refine ⟨37469748088774780996014365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399677312946930997290819893 37469748088774780996014365)
      ·
        refine ⟨14051155533290542873505387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37469748088774780996014365 14051155533290542873505387)
        ·
          refine ⟨21076733299935814310258081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14051155533290542873505387 21076733299935814310258081)
          ·
            refine ⟨15807549974951860732693561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21076733299935814310258081 15807549974951860732693561)
            ·
              refine ⟨11855662481213895549520171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15807549974951860732693561 11855662481213895549520171)
              ·
                refine ⟨17783493721820843324280257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11855662481213895549520171 17783493721820843324280257)
                ·
                  refine ⟨13337620291365632493210193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17783493721820843324280257 13337620291365632493210193)
                  ·
                    refine ⟨10003215218524224369907645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13337620291365632493210193 10003215218524224369907645)
                    ·
                      refine ⟨3751205706946584138715367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003215218524224369907645 3751205706946584138715367)
                      ·
                        rfl

theorem cell23_7305447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7305447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305447 prefixEnd_7305447 := by exact prefixLift 7305447
  have htrace : WordTrace (prefixWord ++ tailWord_7305447) baseStart_7305447 baseEnd_7305447 := by
    simpa [prefixWord, tailWord_7305447, baseEnd_7305447] using wordTrace_append hprefix tailTrace_7305447
  have hstable : (prefixWord ++ tailWord_7305447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305447).length < 2 ^ (prefixWord ++ tailWord_7305447).sum := by decide
  have hdescent : baseEnd_7305447 < baseStart_7305447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305456 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_7305456 : Nat := 118140960795 + 7305456 * 2 ^ 59
def prefixEnd_7305456 : Nat := 4983230072969 + 3 ^ 40 * 7305456 * 2
def baseEnd_7305456 : Nat := 3751210328272474603502825

theorem tailTrace_7305456 : CollatzResearch.WordTrace tailWord_7305456 prefixEnd_7305456 3751210328272474603502825 := by
  unfold tailWord_7305456
  simp only [CollatzResearch.WordTrace]
  refine ⟨133225935110794029698812111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177634580147725372931749481 133225935110794029698812111)
  ·
    refine ⟨199838902666191044548218167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133225935110794029698812111 199838902666191044548218167)
    ·
      refine ⟨299758353999286566822327251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199838902666191044548218167 299758353999286566822327251)
      ·
        refine ⟨449637530998929850233490877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299758353999286566822327251 449637530998929850233490877)
        ·
          refine ⟨168614074124598693837559079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449637530998929850233490877 168614074124598693837559079)
          ·
            refine ⟨252921111186898040756338619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168614074124598693837559079 252921111186898040756338619)
            ·
              refine ⟨379381666780347061134507929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252921111186898040756338619 379381666780347061134507929)
              ·
                refine ⟨284536250085260295850880947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379381666780347061134507929 284536250085260295850880947)
                ·
                  refine ⟨426804375127890443776321421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284536250085260295850880947 426804375127890443776321421)
                  ·
                    refine ⟨160051640672958916416120533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426804375127890443776321421 160051640672958916416120533)
                    ·
                      refine ⟨3751210328272474603502825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160051640672958916416120533 3751210328272474603502825)
                      ·
                        rfl

theorem cell23_7305456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_7305456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305456 prefixEnd_7305456 := by exact prefixLift 7305456
  have htrace : WordTrace (prefixWord ++ tailWord_7305456) baseStart_7305456 baseEnd_7305456 := by
    simpa [prefixWord, tailWord_7305456, baseEnd_7305456] using wordTrace_append hprefix tailTrace_7305456
  have hstable : (prefixWord ++ tailWord_7305456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305456).length < 2 ^ (prefixWord ++ tailWord_7305456).sum := by decide
  have hdescent : baseEnd_7305456 < baseStart_7305456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305483 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4]
def baseStart_7305483 : Nat := 118140960795 + 7305483 * 2 ^ 59
def prefixEnd_7305483 : Nat := 4983230072969 + 3 ^ 40 * 7305483 * 2
def baseEnd_7305483 : Nat := 3751224192250145997865201

theorem tailTrace_7305483 : CollatzResearch.WordTrace tailWord_7305483 prefixEnd_7305483 3751224192250145997865201 := by
  unfold tailWord_7305483
  simp only [CollatzResearch.WordTrace]
  refine ⟨266452854992490243008857103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177635236661660162005904735 266452854992490243008857103)
  ·
    refine ⟨399679282488735364513285655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266452854992490243008857103 399679282488735364513285655)
    ·
      refine ⟨599518923733103046769928483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399679282488735364513285655 599518923733103046769928483)
      ·
        refine ⟨899278385599654570154892725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599518923733103046769928483 899278385599654570154892725)
        ·
          refine ⟨84307348649967615952021193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 899278385599654570154892725 84307348649967615952021193)
          ·
            refine ⟨63230511487475711964015895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84307348649967615952021193 63230511487475711964015895)
            ·
              refine ⟨94845767231213567946023843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63230511487475711964015895 94845767231213567946023843)
              ·
                refine ⟨142268650846820351919035765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94845767231213567946023843 142268650846820351919035765)
                ·
                  refine ⟨13337686016889407992409603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142268650846820351919035765 13337686016889407992409603)
                  ·
                    refine ⟨20006529025334111988614405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13337686016889407992409603 20006529025334111988614405)
                    ·
                      refine ⟨3751224192250145997865201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20006529025334111988614405 3751224192250145997865201)
                      ·
                        rfl

theorem cell23_7305483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4].length) (baseStart_7305483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305483 prefixEnd_7305483 := by exact prefixLift 7305483
  have htrace : WordTrace (prefixWord ++ tailWord_7305483) baseStart_7305483 baseEnd_7305483 := by
    simpa [prefixWord, tailWord_7305483, baseEnd_7305483] using wordTrace_append hprefix tailTrace_7305483
  have hstable : (prefixWord ++ tailWord_7305483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305483).length < 2 ^ (prefixWord ++ tailWord_7305483).sum := by decide
  have hdescent : baseEnd_7305483 < baseStart_7305483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305493 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_7305493 : Nat := 118140960795 + 7305493 * 2 ^ 59
def prefixEnd_7305493 : Nat := 4983230072969 + 3 ^ 40 * 7305493 * 2
def baseEnd_7305493 : Nat := 1250409775685563652913385

theorem tailTrace_7305493 : CollatzResearch.WordTrace tailWord_7305493 prefixEnd_7305493 1250409775685563652913385 := by
  unfold tailWord_7305493
  simp only [CollatzResearch.WordTrace]
  refine ⟨266453219722454014716721133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177635479814969343144480755 266453219722454014716721133)
  ·
    refine ⟨99919957395920255518770425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266453219722454014716721133 99919957395920255518770425)
    ·
      refine ⟨74939968046940191639077819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99919957395920255518770425 74939968046940191639077819)
      ·
        refine ⟨112409952070410287458616729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74939968046940191639077819 112409952070410287458616729)
        ·
          refine ⟨84307464052807715593962547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112409952070410287458616729 84307464052807715593962547)
          ·
            refine ⟨126461196079211573390943821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84307464052807715593962547 126461196079211573390943821)
            ·
              refine ⟨47422948529704340021603933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126461196079211573390943821 47422948529704340021603933)
              ·
                refine ⟨17783605698639127508101475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47422948529704340021603933 17783605698639127508101475)
                ·
                  refine ⟨26675408547958691262152213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17783605698639127508101475 26675408547958691262152213)
                  ·
                    refine ⟨1250409775685563652913385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26675408547958691262152213 1250409775685563652913385)
                    ·
                      rfl

theorem cell23_7305493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_7305493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305493 prefixEnd_7305493 := by exact prefixLift 7305493
  have htrace : WordTrace (prefixWord ++ tailWord_7305493) baseStart_7305493 baseEnd_7305493 := by
    simpa [prefixWord, tailWord_7305493, baseEnd_7305493] using wordTrace_append hprefix tailTrace_7305493
  have hstable : (prefixWord ++ tailWord_7305493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305493).length < 2 ^ (prefixWord ++ tailWord_7305493).sum := by decide
  have hdescent : baseEnd_7305493 < baseStart_7305493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7305500 : Nat := 118140960795 + 7305500 * 2 ^ 59
def prefixEnd_7305500 : Nat := 4983230072969 + 3 ^ 40 * 7305500 * 2
def baseEnd_7305500 : Nat := 3751232921421272431352623

theorem tailTrace_7305500 : CollatzResearch.WordTrace tailWord_7305500 prefixEnd_7305500 3751232921421272431352623 := by
  unfold tailWord_7305500
  simp only [CollatzResearch.WordTrace]
  refine ⟨133226737516714327456112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177635650022285769941483969 133226737516714327456112977)
  ·
    refine ⟨99920053137535745592084733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133226737516714327456112977 99920053137535745592084733)
    ·
      refine ⟨37470019926575904597031775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99920053137535745592084733 37470019926575904597031775)
      ·
        refine ⟨56205029889863856895547663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37470019926575904597031775 56205029889863856895547663)
        ·
          refine ⟨84307544834795785343321495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56205029889863856895547663 84307544834795785343321495)
          ·
            refine ⟨126461317252193678014982243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84307544834795785343321495 126461317252193678014982243)
            ·
              refine ⟨189691975878290517022473365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126461317252193678014982243 189691975878290517022473365)
              ·
                refine ⟨8891811369294867985428439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189691975878290517022473365 8891811369294867985428439)
                ·
                  refine ⟨13337717053942301978142659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8891811369294867985428439 13337717053942301978142659)
                  ·
                    refine ⟨20006575580913452967213989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13337717053942301978142659 20006575580913452967213989)
                    ·
                      refine ⟨3751232921421272431352623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20006575580913452967213989 3751232921421272431352623)
                      ·
                        rfl

theorem cell23_7305500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7305500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305500 prefixEnd_7305500 := by exact prefixLift 7305500
  have htrace : WordTrace (prefixWord ++ tailWord_7305500) baseStart_7305500 baseEnd_7305500 := by
    simpa [prefixWord, tailWord_7305500, baseEnd_7305500] using wordTrace_append hprefix tailTrace_7305500
  have hstable : (prefixWord ++ tailWord_7305500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305500).length < 2 ^ (prefixWord ++ tailWord_7305500).sum := by decide
  have hdescent : baseEnd_7305500 < baseStart_7305500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305504 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7305504 : Nat := 118140960795 + 7305504 * 2 ^ 59
def prefixEnd_7305504 : Nat := 4983230072969 + 3 ^ 40 * 7305504 * 2
def baseEnd_7305504 : Nat := 3751234975343890415702605

theorem tailTrace_7305504 : CollatzResearch.WordTrace tailWord_7305504 prefixEnd_7305504 3751234975343890415702605 := by
  unfold tailWord_7305504
  simp only [CollatzResearch.WordTrace]
  refine ⟨133226810462707081797685783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177635747283609442396914377 133226810462707081797685783)
  ·
    refine ⟨199840215694060622696528675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133226810462707081797685783 199840215694060622696528675)
    ·
      refine ⟨299760323541090934044793013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199840215694060622696528675 299760323541090934044793013)
      ·
        refine ⟨28102530331977275066699345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299760323541090934044793013 28102530331977275066699345)
        ·
          refine ⟨21076897748982956300024509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28102530331977275066699345 21076897748982956300024509)
          ·
            refine ⟨7903836655868608612509191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21076897748982956300024509 7903836655868608612509191)
            ·
              refine ⟨11855754983802912918763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903836655868608612509191 11855754983802912918763787)
              ·
                refine ⟨17783632475704369378145681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11855754983802912918763787 17783632475704369378145681)
                ·
                  refine ⟨13337724356778277033609261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17783632475704369378145681 13337724356778277033609261)
                  ·
                    refine ⟨5001646633791853887603473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13337724356778277033609261 5001646633791853887603473)
                    ·
                      refine ⟨3751234975343890415702605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001646633791853887603473 3751234975343890415702605)
                      ·
                        rfl

theorem cell23_7305504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7305504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305504 prefixEnd_7305504 := by exact prefixLift 7305504
  have htrace : WordTrace (prefixWord ++ tailWord_7305504) baseStart_7305504 baseEnd_7305504 := by
    simpa [prefixWord, tailWord_7305504, baseEnd_7305504] using wordTrace_append hprefix tailTrace_7305504
  have hstable : (prefixWord ++ tailWord_7305504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305504).length < 2 ^ (prefixWord ++ tailWord_7305504).sum := by decide
  have hdescent : baseEnd_7305504 < baseStart_7305504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305534 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_7305534 : Nat := 118140960795 + 7305534 * 2 ^ 59
def prefixEnd_7305534 : Nat := 4983230072969 + 3 ^ 40 * 7305534 * 2
def baseEnd_7305534 : Nat := 3751250379763525298327467

theorem tailTrace_7305534 : CollatzResearch.WordTrace tailWord_7305534 prefixEnd_7305534 3751250379763525298327467 := by
  unfold tailWord_7305534
  simp only [CollatzResearch.WordTrace]
  refine ⟨33306839389413184839870457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177636476743536985812642437 33306839389413184839870457)
  ·
    refine ⟨24980129542059888629902843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33306839389413184839870457 24980129542059888629902843)
    ·
      refine ⟨37470194313089832944854265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24980129542059888629902843 37470194313089832944854265)
      ·
        refine ⟨28102645734817374708640699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37470194313089832944854265 28102645734817374708640699)
        ·
          refine ⟨42153968602226062062961049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28102645734817374708640699 42153968602226062062961049)
          ·
            refine ⟨31615476451669546547220787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42153968602226062062961049 31615476451669546547220787)
            ·
              refine ⟨47423214677504319820831181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31615476451669546547220787 47423214677504319820831181)
              ·
                refine ⟨17783705504064119932811693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47423214677504319820831181 17783705504064119932811693)
                ·
                  refine ⟨6668889564024044974804385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17783705504064119932811693 6668889564024044974804385)
                  ·
                    refine ⟨5001667173018033731103289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668889564024044974804385 5001667173018033731103289)
                    ·
                      refine ⟨3751250379763525298327467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001667173018033731103289 3751250379763525298327467)
                      ·
                        rfl

theorem cell23_7305534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_7305534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305534 prefixEnd_7305534 := by exact prefixLift 7305534
  have htrace : WordTrace (prefixWord ++ tailWord_7305534) baseStart_7305534 baseEnd_7305534 := by
    simpa [prefixWord, tailWord_7305534, baseEnd_7305534] using wordTrace_append hprefix tailTrace_7305534
  have hstable : (prefixWord ++ tailWord_7305534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305534).length < 2 ^ (prefixWord ++ tailWord_7305534).sum := by decide
  have hdescent : baseEnd_7305534 < baseStart_7305534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305537 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7305537 : Nat := 118140960795 + 7305537 * 2 ^ 59
def prefixEnd_7305537 : Nat := 4983230072969 + 3 ^ 40 * 7305537 * 2
def baseEnd_7305537 : Nat := 3751251920205488786589953

theorem tailTrace_7305537 : CollatzResearch.WordTrace tailWord_7305537 prefixEnd_7305537 3751251920205488786589953 := by
  unfold tailWord_7305537
  simp only [CollatzResearch.WordTrace]
  refine ⟨266454824534294610231322865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177636549689529740154215243 266454824534294610231322865)
  ·
    refine ⟨199841118400720957673492149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266454824534294610231322865 199841118400720957673492149)
    ·
      refine ⟨18735104850067589781889889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199841118400720957673492149 18735104850067589781889889)
      ·
        refine ⟨14051328637550692336417417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18735104850067589781889889 14051328637550692336417417)
        ·
          refine ⟨10538496478163019252313063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14051328637550692336417417 10538496478163019252313063)
          ·
            refine ⟨15807744717244528878469595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538496478163019252313063 15807744717244528878469595)
            ·
              refine ⟨23711617075866793317704393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15807744717244528878469595 23711617075866793317704393)
              ·
                refine ⟨17783712806900094988278295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23711617075866793317704393 17783712806900094988278295)
                ·
                  refine ⟨26675569210350142482417443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17783712806900094988278295 26675569210350142482417443)
                  ·
                    refine ⟨40013353815525213723626165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26675569210350142482417443 40013353815525213723626165)
                    ·
                      refine ⟨3751251920205488786589953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40013353815525213723626165 3751251920205488786589953)
                      ·
                        rfl

theorem cell23_7305537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7305537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305537 prefixEnd_7305537 := by exact prefixLift 7305537
  have htrace : WordTrace (prefixWord ++ tailWord_7305537) baseStart_7305537 baseEnd_7305537 := by
    simpa [prefixWord, tailWord_7305537, baseEnd_7305537] using wordTrace_append hprefix tailTrace_7305537
  have hstable : (prefixWord ++ tailWord_7305537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305537).length < 2 ^ (prefixWord ++ tailWord_7305537).sum := by decide
  have hdescent : baseEnd_7305537 < baseStart_7305537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305550 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_7305550 : Nat := 118140960795 + 7305550 * 2 ^ 59
def prefixEnd_7305550 : Nat := 4983230072969 + 3 ^ 40 * 7305550 * 2
def baseEnd_7305550 : Nat := 3751258595453997235727393

theorem tailTrace_7305550 : CollatzResearch.WordTrace tailWord_7305550 prefixEnd_7305550 3751258595453997235727393 := by
  unfold tailWord_7305550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33306912335405939181443263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177636865788831675634364069 33306912335405939181443263)
  ·
    refine ⟨49960368503108908772164895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33306912335405939181443263 49960368503108908772164895)
    ·
      refine ⟨74940552754663363158247343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49960368503108908772164895 74940552754663363158247343)
      ·
        refine ⟨112410829131995044737371015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74940552754663363158247343 112410829131995044737371015)
        ·
          refine ⟨168616243697992567106056523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112410829131995044737371015 168616243697992567106056523)
          ·
            refine ⟨252924365546988850659084785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168616243697992567106056523 252924365546988850659084785)
            ·
              refine ⟨189693274160241637994313589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252924365546988850659084785 189693274160241637994313589)
              ·
                refine ⟨17783744452522653561966899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189693274160241637994313589 17783744452522653561966899)
                ·
                  refine ⟨26675616678783980342950349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17783744452522653561966899 26675616678783980342950349)
                  ·
                    refine ⟨10003356254543992628606381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26675616678783980342950349 10003356254543992628606381)
                    ·
                      refine ⟨3751258595453997235727393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003356254543992628606381 3751258595453997235727393)
                      ·
                        rfl

theorem cell23_7305550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_7305550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305550 prefixEnd_7305550 := by exact prefixLift 7305550
  have htrace : WordTrace (prefixWord ++ tailWord_7305550) baseStart_7305550 baseEnd_7305550 := by
    simpa [prefixWord, tailWord_7305550, baseEnd_7305550] using wordTrace_append hprefix tailTrace_7305550
  have hstable : (prefixWord ++ tailWord_7305550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305550).length < 2 ^ (prefixWord ++ tailWord_7305550).sum := by decide
  have hdescent : baseEnd_7305550 < baseStart_7305550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305557 : List Nat := [1, 3, 2, 2, 4, 2, 2, 7]
def baseStart_7305557 : Nat := 118140960795 + 7305557 * 2 ^ 59
def prefixEnd_7305557 : Nat := 4983230072969 + 3 ^ 40 * 7305557 * 2
def baseEnd_7305557 : Nat := 138935636659947359568143

theorem tailTrace_7305557 : CollatzResearch.WordTrace tailWord_7305557 prefixEnd_7305557 138935636659947359568143 := by
  unfold tailWord_7305557
  simp only [CollatzResearch.WordTrace]
  refine ⟨266455553994222153647050925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177637035996148102431367283 266455553994222153647050925)
  ·
    refine ⟨99920832747833307617644097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266455553994222153647050925 99920832747833307617644097)
    ·
      refine ⟨74940624560874980713233073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99920832747833307617644097 74940624560874980713233073)
      ·
        refine ⟨56205468420656235534924805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74940624560874980713233073 56205468420656235534924805)
        ·
          refine ⟨10538525328873044162798401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56205468420656235534924805 10538525328873044162798401)
          ·
            refine ⟨7903893996654783122098801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10538525328873044162798401 7903893996654783122098801)
            ·
              refine ⟨5927920497491087341574101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7903893996654783122098801 5927920497491087341574101)
              ·
                refine ⟨138935636659947359568143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5927920497491087341574101 138935636659947359568143)
                ·
                  rfl

theorem cell23_7305557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 7].length) (baseStart_7305557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305557 prefixEnd_7305557 := by exact prefixLift 7305557
  have htrace : WordTrace (prefixWord ++ tailWord_7305557) baseStart_7305557 baseEnd_7305557 := by
    simpa [prefixWord, tailWord_7305557, baseEnd_7305557] using wordTrace_append hprefix tailTrace_7305557
  have hstable : (prefixWord ++ tailWord_7305557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305557).length < 2 ^ (prefixWord ++ tailWord_7305557).sum := by decide
  have hdescent : baseEnd_7305557 < baseStart_7305557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305568 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 1, 2, 2]
def baseStart_7305568 : Nat := 118140960795 + 7305568 * 2 ^ 59
def prefixEnd_7305568 : Nat := 4983230072969 + 3 ^ 40 * 7305568 * 2
def baseEnd_7305568 : Nat := 3751267838105778165302311

theorem tailTrace_7305568 : CollatzResearch.WordTrace tailWord_7305568 prefixEnd_7305568 3751267838105778165302311 := by
  unfold tailWord_7305568
  simp only [CollatzResearch.WordTrace]
  refine ⟨133227977598591151262850679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177637303464788201683800905 133227977598591151262850679)
  ·
    refine ⟨199841966397886726894276019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133227977598591151262850679 199841966397886726894276019)
    ·
      refine ⟨299762949596830090341414029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199841966397886726894276019 299762949596830090341414029)
      ·
        refine ⟨112411106098811283878030261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299762949596830090341414029 112411106098811283878030261)
        ·
          refine ⟨10538541196763557863565337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112411106098811283878030261 10538541196763557863565337)
          ·
            refine ⟨7903905897572668397674003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10538541196763557863565337 7903905897572668397674003)
            ·
              refine ⟨11855858846359002596511005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903905897572668397674003 11855858846359002596511005)
              ·
                refine ⟨4445947067384625973691627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855858846359002596511005 4445947067384625973691627)
                ·
                  refine ⟨6668920601076938960537441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445947067384625973691627 6668920601076938960537441)
                  ·
                    refine ⟨5001690450807704220403081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668920601076938960537441 5001690450807704220403081)
                    ·
                      refine ⟨3751267838105778165302311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001690450807704220403081 3751267838105778165302311)
                      ·
                        rfl

theorem cell23_7305568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_7305568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305568 prefixEnd_7305568 := by exact prefixLift 7305568
  have htrace : WordTrace (prefixWord ++ tailWord_7305568) baseStart_7305568 baseEnd_7305568 := by
    simpa [prefixWord, tailWord_7305568, baseEnd_7305568] using wordTrace_append hprefix tailTrace_7305568
  have hstable : (prefixWord ++ tailWord_7305568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305568).length < 2 ^ (prefixWord ++ tailWord_7305568).sum := by decide
  have hdescent : baseEnd_7305568 < baseStart_7305568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305577 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 1, 3, 2]
def baseStart_7305577 : Nat := 118140960795 + 7305577 * 2 ^ 59
def prefixEnd_7305577 : Nat := 4983230072969 + 3 ^ 40 * 7305577 * 2
def baseEnd_7305577 : Nat := 3751272459431668630089769

theorem tailTrace_7305577 : CollatzResearch.WordTrace tailWord_7305577 prefixEnd_7305577 3751272459431668630089769 := by
  unfold tailWord_7305577
  simp only [CollatzResearch.WordTrace]
  refine ⟨266456283454149697062778985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177637522302766464708519323 266456283454149697062778985)
  ·
    refine ⟨199842212590612272797084239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266456283454149697062778985 199842212590612272797084239)
    ·
      refine ⟨299763318885918409195626359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199842212590612272797084239 299763318885918409195626359)
      ·
        refine ⟨449644978328877613793439539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299763318885918409195626359 449644978328877613793439539)
        ·
          refine ⟨674467467493316420690159309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449644978328877613793439539 674467467493316420690159309)
          ·
            refine ⟨252925300309993657758809741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674467467493316420690159309 252925300309993657758809741)
            ·
              refine ⟨94846987616247621659553653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252925300309993657758809741 94846987616247621659553653)
              ·
                refine ⟨8891905089023214530583155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94846987616247621659553653 8891905089023214530583155)
                ·
                  refine ⟨13337857633534821795874733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8891905089023214530583155 13337857633534821795874733)
                  ·
                    refine ⟨5001696612575558173453025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13337857633534821795874733 5001696612575558173453025)
                    ·
                      refine ⟨3751272459431668630089769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001696612575558173453025 3751272459431668630089769)
                      ·
                        rfl

theorem cell23_7305577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3, 2].length) (baseStart_7305577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305577 prefixEnd_7305577 := by exact prefixLift 7305577
  have htrace : WordTrace (prefixWord ++ tailWord_7305577) baseStart_7305577 baseEnd_7305577 := by
    simpa [prefixWord, tailWord_7305577, baseEnd_7305577] using wordTrace_append hprefix tailTrace_7305577
  have hstable : (prefixWord ++ tailWord_7305577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305577).length < 2 ^ (prefixWord ++ tailWord_7305577).sum := by decide
  have hdescent : baseEnd_7305577 < baseStart_7305577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305583 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 2, 6]
def baseStart_7305583 : Nat := 118140960795 + 7305583 * 2 ^ 59
def prefixEnd_7305583 : Nat := 4983230072969 + 3 ^ 40 * 7305583 * 2
def baseEnd_7305583 : Nat := 1250425180105198535538247

theorem tailTrace_7305583 : CollatzResearch.WordTrace tailWord_7305583 prefixEnd_7305583 1250425180105198535538247 := by
  unfold tailWord_7305583
  simp only [CollatzResearch.WordTrace]
  refine ⟨266456502292127960087497403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177637668194751973391664935 266456502292127960087497403)
  ·
    refine ⟨399684753438191940131246105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266456502292127960087497403 399684753438191940131246105)
    ·
      refine ⟨299763565078643955098434579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399684753438191940131246105 299763565078643955098434579)
      ·
        refine ⟨449645347617965932647651869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299763565078643955098434579 449645347617965932647651869)
        ·
          refine ⟨168617005356737224742869451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449645347617965932647651869 168617005356737224742869451)
          ·
            refine ⟨252925508035105837114304177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168617005356737224742869451 252925508035105837114304177)
            ·
              refine ⟨189694131026329377835728133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252925508035105837114304177 189694131026329377835728133)
              ·
                refine ⟨35567649567436758344199025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189694131026329377835728133 35567649567436758344199025)
                ·
                  refine ⟨26675737175577568758149269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35567649567436758344199025 26675737175577568758149269)
                  ·
                    refine ⟨1250425180105198535538247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26675737175577568758149269 1250425180105198535538247)
                    ·
                      rfl

theorem cell23_7305583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_7305583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305583 prefixEnd_7305583 := by exact prefixLift 7305583
  have htrace : WordTrace (prefixWord ++ tailWord_7305583) baseStart_7305583 baseEnd_7305583 := by
    simpa [prefixWord, tailWord_7305583, baseEnd_7305583] using wordTrace_append hprefix tailTrace_7305583
  have hstable : (prefixWord ++ tailWord_7305583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305583).length < 2 ^ (prefixWord ++ tailWord_7305583).sum := by decide
  have hdescent : baseEnd_7305583 < baseStart_7305583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305593 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7305593 : Nat := 118140960795 + 7305593 * 2 ^ 59
def prefixEnd_7305593 : Nat := 4983230072969 + 3 ^ 40 * 7305593 * 2
def baseEnd_7305593 : Nat := 3751280675122140567489695

theorem tailTrace_7305593 : CollatzResearch.WordTrace tailWord_7305593 prefixEnd_7305593 3751280675122140567489695 := by
  unfold tailWord_7305593
  simp only [CollatzResearch.WordTrace]
  refine ⟨266456867022091731795361433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177637911348061154530240955 266456867022091731795361433)
  ·
    refine ⟨199842650266568798846521075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266456867022091731795361433 199842650266568798846521075)
    ·
      refine ⟨299763975399853198269781613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199842650266568798846521075 299763975399853198269781613)
      ·
        refine ⟨112411490774944949351168105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299763975399853198269781613 112411490774944949351168105)
        ·
          refine ⟨84308618081208712013376079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112411490774944949351168105 84308618081208712013376079)
          ·
            refine ⟨126462927121813068020064119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84308618081208712013376079 126462927121813068020064119)
            ·
              refine ⟨189694390682719602030096179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126462927121813068020064119 189694390682719602030096179)
              ·
                refine ⟨284541586024079403045144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189694390682719602030096179 284541586024079403045144269)
                ·
                  refine ⟨106703094759029776141929101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284541586024079403045144269 106703094759029776141929101)
                  ·
                    refine ⟨40013660534636166053223413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106703094759029776141929101 40013660534636166053223413)
                    ·
                      refine ⟨3751280675122140567489695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40013660534636166053223413 3751280675122140567489695)
                      ·
                        rfl

theorem cell23_7305593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7305593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305593 prefixEnd_7305593 := by exact prefixLift 7305593
  have htrace : WordTrace (prefixWord ++ tailWord_7305593) baseStart_7305593 baseEnd_7305593 := by
    simpa [prefixWord, tailWord_7305593, baseEnd_7305593] using wordTrace_append hprefix tailTrace_7305593
  have hstable : (prefixWord ++ tailWord_7305593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305593).length < 2 ^ (prefixWord ++ tailWord_7305593).sum := by decide
  have hdescent : baseEnd_7305593 < baseStart_7305593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305601 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7305601 : Nat := 118140960795 + 7305601 * 2 ^ 59
def prefixEnd_7305601 : Nat := 4983230072969 + 3 ^ 40 * 7305601 * 2
def baseEnd_7305601 : Nat := 3751284782967376536189659

theorem tailTrace_7305601 : CollatzResearch.WordTrace tailWord_7305601 prefixEnd_7305601 3751284782967376536189659 := by
  unfold tailWord_7305601
  simp only [CollatzResearch.WordTrace]
  refine ⟨266457158806062749161652657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177638105870708499441101771 266457158806062749161652657)
  ·
    refine ⟨199842869104547061871239493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266457158806062749161652657 199842869104547061871239493)
    ·
      refine ⟨37470537957102574100857405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199842869104547061871239493 37470537957102574100857405)
      ·
        refine ⟨14051451733913465287821527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37470537957102574100857405 14051451733913465287821527)
        ·
          refine ⟨21077177600870197931732291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14051451733913465287821527 21077177600870197931732291)
          ·
            refine ⟨31615766401305296897598437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21077177600870197931732291 31615766401305296897598437)
            ·
              refine ⟨5927956200244743168299707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31615766401305296897598437 5927956200244743168299707)
              ·
                refine ⟨8891934300367114752449561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927956200244743168299707 8891934300367114752449561)
                ·
                  refine ⟨6668950725275336064337171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8891934300367114752449561 6668950725275336064337171)
                  ·
                    refine ⟨10003426087913004096505757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668950725275336064337171 10003426087913004096505757)
                    ·
                      refine ⟨3751284782967376536189659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10003426087913004096505757 3751284782967376536189659)
                      ·
                        rfl

theorem cell23_7305601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7305601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305601 prefixEnd_7305601 := by exact prefixLift 7305601
  have htrace : WordTrace (prefixWord ++ tailWord_7305601) baseStart_7305601 baseEnd_7305601 := by
    simpa [prefixWord, tailWord_7305601, baseEnd_7305601] using wordTrace_append hprefix tailTrace_7305601
  have hstable : (prefixWord ++ tailWord_7305601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305601).length < 2 ^ (prefixWord ++ tailWord_7305601).sum := by decide
  have hdescent : baseEnd_7305601 < baseStart_7305601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305607 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_7305607 : Nat := 118140960795 + 7305607 * 2 ^ 59
def prefixEnd_7305607 : Nat := 4983230072969 + 3 ^ 40 * 7305607 * 2
def baseEnd_7305607 : Nat := 3751287863851303512714631

theorem tailTrace_7305607 : CollatzResearch.WordTrace tailWord_7305607 prefixEnd_7305607 3751287863851303512714631 := by
  unfold tailWord_7305607
  simp only [CollatzResearch.WordTrace]
  refine ⟨266457377644041012186371075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177638251762694008124247383 266457377644041012186371075)
  ·
    refine ⟨399686066466061518279556613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266457377644041012186371075 399686066466061518279556613)
    ·
      refine ⟨74941137462386534677416865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 399686066466061518279556613 74941137462386534677416865)
      ·
        refine ⟨56205853096789901008062649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74941137462386534677416865 56205853096789901008062649)
        ·
          refine ⟨42154389822592425756046987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56205853096789901008062649 42154389822592425756046987)
          ·
            refine ⟨63231584733888638634070481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42154389822592425756046987 63231584733888638634070481)
            ·
              refine ⟨47423688550416478975552861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63231584733888638634070481 47423688550416478975552861)
              ·
                refine ⟨17783883206406179615832323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47423688550416478975552861 17783883206406179615832323)
                ·
                  refine ⟨26675824809609269423748485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17783883206406179615832323 26675824809609269423748485)
                  ·
                    refine ⟨5001717151801738016952841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26675824809609269423748485 5001717151801738016952841)
                    ·
                      refine ⟨3751287863851303512714631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001717151801738016952841 3751287863851303512714631)
                      ·
                        rfl

theorem cell23_7305607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_7305607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305607 prefixEnd_7305607 := by exact prefixLift 7305607
  have htrace : WordTrace (prefixWord ++ tailWord_7305607) baseStart_7305607 baseEnd_7305607 := by
    simpa [prefixWord, tailWord_7305607, baseEnd_7305607] using wordTrace_append hprefix tailTrace_7305607
  have hstable : (prefixWord ++ tailWord_7305607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305607).length < 2 ^ (prefixWord ++ tailWord_7305607).sum := by decide
  have hdescent : baseEnd_7305607 < baseStart_7305607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7305624 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7305624 : Nat := 118140960795 + 7305624 * 2 ^ 59
def prefixEnd_7305624 : Nat := 4983230072969 + 3 ^ 40 * 7305624 * 2
def baseEnd_7305624 : Nat := 3751296593022429946202053

theorem tailTrace_7305624 : CollatzResearch.WordTrace tailWord_7305624 prefixEnd_7305624 3751296593022429946202053 := by
  unfold tailWord_7305624
  simp only [CollatzResearch.WordTrace]
  refine ⟨133228998842489712044869963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177638665123319616059826617 133228998842489712044869963)
  ·
    refine ⟨199843498263734568067304945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133228998842489712044869963 199843498263734568067304945)
    ·
      refine ⟨149882623697800926050478709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199843498263734568067304945 149882623697800926050478709)
      ·
        refine ⟨14051495971668836817232379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149882623697800926050478709 14051495971668836817232379)
        ·
          refine ⟨21077243957503255225848569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14051495971668836817232379 21077243957503255225848569)
          ·
            refine ⟨15807932968127441419386427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21077243957503255225848569 15807932968127441419386427)
            ·
              refine ⟨23711899452191162129079641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15807932968127441419386427 23711899452191162129079641)
              ·
                refine ⟨17783924589143371596809731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23711899452191162129079641 17783924589143371596809731)
                ·
                  refine ⟨26675886883715057395214597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17783924589143371596809731 26675886883715057395214597)
                  ·
                    refine ⟨5001728790696573261602737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26675886883715057395214597 5001728790696573261602737)
                    ·
                      refine ⟨3751296593022429946202053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5001728790696573261602737 3751296593022429946202053)
                      ·
                        rfl

theorem cell23_7305624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7305624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7305624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7305624 prefixEnd_7305624 := by exact prefixLift 7305624
  have htrace : WordTrace (prefixWord ++ tailWord_7305624) baseStart_7305624 baseEnd_7305624 := by
    simpa [prefixWord, tailWord_7305624, baseEnd_7305624] using wordTrace_append hprefix tailTrace_7305624
  have hstable : (prefixWord ++ tailWord_7305624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7305624).length < 2 ^ (prefixWord ++ tailWord_7305624).sum := by decide
  have hdescent : baseEnd_7305624 < baseStart_7305624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7305624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
