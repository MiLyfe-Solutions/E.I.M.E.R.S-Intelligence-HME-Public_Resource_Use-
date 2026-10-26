import V185TrunkScan22Chunk344

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3078862 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_3078862 : Nat := 118140960795 + 3078862 * 2 ^ 59
def prefixEnd_3078862 : Nat := 4983230072969 + 3 ^ 40 * 3078862 * 2
def baseEnd_3078862 : Nat := 351319127747386260436795

theorem tailTrace_3078862 : CollatzResearch.WordTrace tailWord_3078862 prefixEnd_3078862 351319127747386260436795 := by
  unfold tailWord_3078862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036915321477034576427855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74863548381210851074281893 14036915321477034576427855)
  ·
    refine ⟨21055372982215551864641783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14036915321477034576427855 21055372982215551864641783)
    ·
      refine ⟨31583059473323327796962675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21055372982215551864641783 31583059473323327796962675)
      ·
        refine ⟨47374589209984991695444013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31583059473323327796962675 47374589209984991695444013)
        ·
          refine ⟨17765470953744371885791505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47374589209984991695444013 17765470953744371885791505)
          ·
            refine ⟨13324103215308278914343629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17765470953744371885791505 13324103215308278914343629)
            ·
              refine ⟨4996538705740604592878861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13324103215308278914343629 4996538705740604592878861)
              ·
                refine ⟨1873702014652726722329573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4996538705740604592878861 1873702014652726722329573)
                ·
                  refine ⟨351319127747386260436795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873702014652726722329573 351319127747386260436795)
                  ·
                    rfl

theorem cell22_3078862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_3078862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078862 prefixEnd_3078862 := by exact prefixLift 3078862
  have htrace : WordTrace (prefixWord ++ tailWord_3078862) baseStart_3078862 baseEnd_3078862 := by
    simpa [prefixWord, tailWord_3078862, baseEnd_3078862] using wordTrace_append hprefix tailTrace_3078862
  have hstable : (prefixWord ++ tailWord_3078862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078862).length < 2 ^ (prefixWord ++ tailWord_3078862).sum := by decide
  have hdescent : baseEnd_3078862 < baseStart_3078862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078894 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3078894 : Nat := 118140960795 + 3078894 * 2 ^ 59
def prefixEnd_3078894 : Nat := 4983230072969 + 3 ^ 40 * 3078894 * 2
def baseEnd_3078894 : Nat := 1053968337496121364510287

theorem tailTrace_3078894 : CollatzResearch.WordTrace tailWord_3078894 prefixEnd_3078894 1053968337496121364510287 := by
  unfold tailWord_3078894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037061213462543259573467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74864326471800230717725157 14037061213462543259573467)
  ·
    refine ⟨21055591820193814889360201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14037061213462543259573467 21055591820193814889360201)
    ·
      refine ⟨15791693865145361167020151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21055591820193814889360201 15791693865145361167020151)
      ·
        refine ⟨23687540797718041750530227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791693865145361167020151 23687540797718041750530227)
        ·
          refine ⟨35531311196577062625795341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23687540797718041750530227 35531311196577062625795341)
          ·
            refine ⟨13324241698716398484673253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35531311196577062625795341 13324241698716398484673253)
            ·
              refine ⟨2498295318509324715876235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13324241698716398484673253 2498295318509324715876235)
              ·
                refine ⟨3747442977763987073814353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498295318509324715876235 3747442977763987073814353)
                ·
                  refine ⟨2810582233322990305360765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747442977763987073814353 2810582233322990305360765)
                  ·
                    refine ⟨1053968337496121364510287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810582233322990305360765 1053968337496121364510287)
                    ·
                      rfl

theorem cell22_3078894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3078894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078894 prefixEnd_3078894 := by exact prefixLift 3078894
  have htrace : WordTrace (prefixWord ++ tailWord_3078894) baseStart_3078894 baseEnd_3078894 := by
    simpa [prefixWord, tailWord_3078894, baseEnd_3078894] using wordTrace_append hprefix tailTrace_3078894
  have hstable : (prefixWord ++ tailWord_3078894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078894).length < 2 ^ (prefixWord ++ tailWord_3078894).sum := by decide
  have hdescent : baseEnd_3078894 < baseStart_3078894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078905 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_3078905 : Nat := 118140960795 + 3078905 * 2 ^ 59
def prefixEnd_3078905 : Nat := 4983230072969 + 3 ^ 40 * 3078905 * 2
def baseEnd_3078905 : Nat := 1053972103020921002485253

theorem tailTrace_3078905 : CollatzResearch.WordTrace tailWord_3078905 prefixEnd_3078905 1053972103020921002485253 := by
  unfold tailWord_3078905
  simp only [CollatzResearch.WordTrace]
  refine ⟨112296890910660494955238169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74864593940440329970158779 112296890910660494955238169)
  ·
    refine ⟨84222668182995371216428627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112296890910660494955238169 84222668182995371216428627)
    ·
      refine ⟨126334002274493056824642941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84222668182995371216428627 126334002274493056824642941)
      ·
        refine ⟨47375250852934896309241103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126334002274493056824642941 47375250852934896309241103)
        ·
          refine ⟨71062876279402344463861655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47375250852934896309241103 71062876279402344463861655)
          ·
            refine ⟨106594314419103516695792483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71062876279402344463861655 106594314419103516695792483)
            ·
              refine ⟨159891471628655275043688725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106594314419103516695792483 159891471628655275043688725)
              ·
                refine ⟨7494912732593216017672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159891471628655275043688725 7494912732593216017672909)
                ·
                  refine ⟨2810592274722456006627341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7494912732593216017672909 2810592274722456006627341)
                  ·
                    refine ⟨1053972103020921002485253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810592274722456006627341 1053972103020921002485253)
                    ·
                      rfl

theorem cell22_3078905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_3078905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078905 prefixEnd_3078905 := by exact prefixLift 3078905
  have htrace : WordTrace (prefixWord ++ tailWord_3078905) baseStart_3078905 baseEnd_3078905 := by
    simpa [prefixWord, tailWord_3078905, baseEnd_3078905] using wordTrace_append hprefix tailTrace_3078905
  have hstable : (prefixWord ++ tailWord_3078905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078905).length < 2 ^ (prefixWord ++ tailWord_3078905).sum := by decide
  have hdescent : baseEnd_3078905 < baseStart_3078905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078997 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 4]
def baseStart_3078997 : Nat := 118140960795 + 3078997 * 2 ^ 59
def prefixEnd_3078997 : Nat := 4983230072969 + 3 ^ 40 * 3078997 * 2
def baseEnd_3078997 : Nat := 351334532167021143061657

theorem tailTrace_3078997 : CollatzResearch.WordTrace tailWord_3078997 prefixEnd_3078997 351334532167021143061657 := by
  unfold tailWord_3078997
  simp only [CollatzResearch.WordTrace]
  refine ⟨112300246426327194667587245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74866830950884796445058163 112300246426327194667587245)
  ·
    refine ⟨42112592409872698000345217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112300246426327194667587245 42112592409872698000345217)
    ·
      refine ⟨31584444307404523500258913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42112592409872698000345217 31584444307404523500258913)
      ·
        refine ⟨23688333230553392625194185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31584444307404523500258913 23688333230553392625194185)
        ·
          refine ⟨17766249922915044468895639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23688333230553392625194185 17766249922915044468895639)
          ·
            refine ⟨26649374884372566703343459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17766249922915044468895639 26649374884372566703343459)
            ·
              refine ⟨39974062326558850055015189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26649374884372566703343459 39974062326558850055015189)
              ·
                refine ⟨1873784171557446096328837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39974062326558850055015189 1873784171557446096328837)
                ·
                  refine ⟨351334532167021143061657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873784171557446096328837 351334532167021143061657)
                  ·
                    rfl

theorem cell22_3078997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_3078997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078997 prefixEnd_3078997 := by exact prefixLift 3078997
  have htrace : WordTrace (prefixWord ++ tailWord_3078997) baseStart_3078997 baseEnd_3078997 := by
    simpa [prefixWord, tailWord_3078997, baseEnd_3078997] using wordTrace_append hprefix tailTrace_3078997
  have hstable : (prefixWord ++ tailWord_3078997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078997).length < 2 ^ (prefixWord ++ tailWord_3078997).sum := by decide
  have hdescent : baseEnd_3078997 < baseStart_3078997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079012 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_3079012 : Nat := 118140960795 + 3079012 * 2 ^ 59
def prefixEnd_3079012 : Nat := 4983230072969 + 3 ^ 40 * 3079012 * 2
def baseEnd_3079012 : Nat := 1054008731307608390059925

theorem tailTrace_3079012 : CollatzResearch.WordTrace tailWord_3079012 prefixEnd_3079012 1054008731307608390059925 := by
  unfold tailWord_3079012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56150396760636426114691645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74867195680848568152922193 56150396760636426114691645)
  ·
    refine ⟨21056398785238659793009367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56150396760636426114691645 21056398785238659793009367)
    ·
      refine ⟨31584598177857989689514051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21056398785238659793009367 31584598177857989689514051)
      ·
        refine ⟨47376897266786984534271077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31584598177857989689514051 47376897266786984534271077)
        ·
          refine ⟨8883168237522559600175827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47376897266786984534271077 8883168237522559600175827)
          ·
            refine ⟨13324752356283839400263741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8883168237522559600175827 13324752356283839400263741)
            ·
              refine ⟨4996782133606439775098903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13324752356283839400263741 4996782133606439775098903)
              ·
                refine ⟨7495173200409659662648355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996782133606439775098903 7495173200409659662648355)
                ·
                  refine ⟨11242759800614489493972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495173200409659662648355 11242759800614489493972533)
                  ·
                    refine ⟨1054008731307608390059925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11242759800614489493972533 1054008731307608390059925)
                    ·
                      rfl

theorem cell22_3079012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_3079012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079012 prefixEnd_3079012 := by exact prefixLift 3079012
  have htrace : WordTrace (prefixWord ++ tailWord_3079012) baseStart_3079012 baseEnd_3079012 := by
    simpa [prefixWord, tailWord_3079012, baseEnd_3079012] using wordTrace_append hprefix tailTrace_3079012
  have hstable : (prefixWord ++ tailWord_3079012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079012).length < 2 ^ (prefixWord ++ tailWord_3079012).sum := by decide
  have hdescent : baseEnd_3079012 < baseStart_3079012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079025 : List Nat := [1, 2, 2, 2, 1, 5, 1, 8]
def baseStart_3079025 : Nat := 118140960795 + 3079025 * 2 ^ 59
def prefixEnd_3079025 : Nat := 4983230072969 + 3 ^ 40 * 3079025 * 2
def baseEnd_3079025 : Nat := 117112575719253409942765

theorem tailTrace_3079025 : CollatzResearch.WordTrace tailWord_3079025 prefixEnd_3079025 117112575719253409942765 := by
  unfold tailWord_3079025
  simp only [CollatzResearch.WordTrace]
  refine ⟨112301267670225755449606529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74867511780150503633071019 112301267670225755449606529)
  ·
    refine ⟨84225950752669316587204897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112301267670225755449606529 84225950752669316587204897)
    ·
      refine ⟨63169463064501987440403673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84225950752669316587204897 63169463064501987440403673)
      ·
        refine ⟨47377097298376490580302755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63169463064501987440403673 47377097298376490580302755)
        ·
          refine ⟨71065645947564735870454133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47377097298376490580302755 71065645947564735870454133)
          ·
            refine ⟨6662404307584193987855075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71065645947564735870454133 6662404307584193987855075)
            ·
              refine ⟨9993606461376290981782613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662404307584193987855075 9993606461376290981782613)
              ·
                refine ⟨117112575719253409942765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9993606461376290981782613 117112575719253409942765)
                ·
                  rfl

theorem cell22_3079025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 8].length) (baseStart_3079025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079025 prefixEnd_3079025 := by exact prefixLift 3079025
  have htrace : WordTrace (prefixWord ++ tailWord_3079025) baseStart_3079025 baseEnd_3079025 := by
    simpa [prefixWord, tailWord_3079025, baseEnd_3079025] using wordTrace_append hprefix tailTrace_3079025
  have hstable : (prefixWord ++ tailWord_3079025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079025).length < 2 ^ (prefixWord ++ tailWord_3079025).sum := by decide
  have hdescent : baseEnd_3079025 < baseStart_3079025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079102 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3079102 : Nat := 118140960795 + 3079102 * 2 ^ 59
def prefixEnd_3079102 : Nat := 4983230072969 + 3 ^ 40 * 3079102 * 2
def baseEnd_3079102 : Nat := 1054039540146878155309649

theorem tailTrace_3079102 : CollatzResearch.WordTrace tailWord_3079102 prefixEnd_3079102 1054039540146878155309649 := by
  unfold tailWord_3079102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14038009511368349700019945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74869384060631198400106373 14038009511368349700019945)
  ·
    refine ⟨10528507133526262275014959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14038009511368349700019945 10528507133526262275014959)
    ·
      refine ⟨15792760700289393412522439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10528507133526262275014959 15792760700289393412522439)
      ·
        refine ⟨23689141050434090118783659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15792760700289393412522439 23689141050434090118783659)
        ·
          refine ⟨35533711575651135178175489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23689141050434090118783659 35533711575651135178175489)
          ·
            refine ⟨26650283681738351383631617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35533711575651135178175489 26650283681738351383631617)
            ·
              refine ⟨19987712761303763537723713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26650283681738351383631617 19987712761303763537723713)
              ·
                refine ⟨14990784570977822653292785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19987712761303763537723713 14990784570977822653292785)
                ·
                  refine ⟨11243088428233366989969589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14990784570977822653292785 11243088428233366989969589)
                  ·
                    refine ⟨1054039540146878155309649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11243088428233366989969589 1054039540146878155309649)
                    ·
                      rfl

theorem cell22_3079102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3079102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079102 prefixEnd_3079102 := by exact prefixLift 3079102
  have htrace : WordTrace (prefixWord ++ tailWord_3079102) baseStart_3079102 baseEnd_3079102 := by
    simpa [prefixWord, tailWord_3079102, baseEnd_3079102] using wordTrace_append hprefix tailTrace_3079102
  have hstable : (prefixWord ++ tailWord_3079102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079102).length < 2 ^ (prefixWord ++ tailWord_3079102).sum := by decide
  have hdescent : baseEnd_3079102 < baseStart_3079102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079110 : List Nat := [6, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3079110 : Nat := 118140960795 + 3079110 * 2 ^ 59
def prefixEnd_3079110 : Nat := 4983230072969 + 3 ^ 40 * 3079110 * 2
def baseEnd_3079110 : Nat := 117115808745596533456625

theorem tailTrace_3079110 : CollatzResearch.WordTrace tailWord_3079110 prefixEnd_3079110 117115808745596533456625 := by
  unfold tailWord_3079110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509511496091181717701587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74869578583278543310967189 3509511496091181717701587)
  ·
    refine ⟨5264267244136772576552381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509511496091181717701587 5264267244136772576552381)
    ·
      refine ⟨1974100216551289716207143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5264267244136772576552381 1974100216551289716207143)
      ·
        refine ⟨2961150324826934574310715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974100216551289716207143 2961150324826934574310715)
        ·
          refine ⟨4441725487240401861466073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961150324826934574310715 4441725487240401861466073)
          ·
            refine ⟨3331294115430301396099555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4441725487240401861466073 3331294115430301396099555)
            ·
              refine ⟨4996941173145452094149333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331294115430301396099555 4996941173145452094149333)
              ·
                refine ⟨117115808745596533456625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4996941173145452094149333 117115808745596533456625)
                ·
                  rfl

theorem cell22_3079110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3079110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079110 prefixEnd_3079110 := by exact prefixLift 3079110
  have htrace : WordTrace (prefixWord ++ tailWord_3079110) baseStart_3079110 baseEnd_3079110 := by
    simpa [prefixWord, tailWord_3079110, baseEnd_3079110] using wordTrace_append hprefix tailTrace_3079110
  have hstable : (prefixWord ++ tailWord_3079110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079110).length < 2 ^ (prefixWord ++ tailWord_3079110).sum := by decide
  have hdescent : baseEnd_3079110 < baseStart_3079110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079151 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 1, 4]
def baseStart_3079151 : Nat := 118140960795 + 3079151 * 2 ^ 59
def prefixEnd_3079151 : Nat := 4983230072969 + 3 ^ 40 * 3079151 * 2
def baseEnd_3079151 : Nat := 1054056313848258360834499

theorem tailTrace_3079151 : CollatzResearch.WordTrace tailWord_3079151 prefixEnd_3079151 1054056313848258360834499 := by
  unfold tailWord_3079151
  simp only [CollatzResearch.WordTrace]
  refine ⟨112305863267769278968693307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74870575511846185979128871 112305863267769278968693307)
  ·
    refine ⟨168458794901653918453039961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112305863267769278968693307 168458794901653918453039961)
    ·
      refine ⟨126344096176240438839779971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168458794901653918453039961 126344096176240438839779971)
      ·
        refine ⟨189516144264360658259669957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126344096176240438839779971 189516144264360658259669957)
        ·
          refine ⟨35534277049567623423688117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189516144264360658259669957 35534277049567623423688117)
          ·
            refine ⟨3331338473396964695970761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35534277049567623423688117 3331338473396964695970761)
            ·
              refine ⟨2498503855047723521978071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3331338473396964695970761 2498503855047723521978071)
              ·
                refine ⟨3747755782571585282967107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498503855047723521978071 3747755782571585282967107)
                ·
                  refine ⟨5621633673857377924450661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747755782571585282967107 5621633673857377924450661)
                  ·
                    refine ⟨1054056313848258360834499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5621633673857377924450661 1054056313848258360834499)
                    ·
                      rfl

theorem cell22_3079151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_3079151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079151 prefixEnd_3079151 := by exact prefixLift 3079151
  have htrace : WordTrace (prefixWord ++ tailWord_3079151) baseStart_3079151 baseEnd_3079151 := by
    simpa [prefixWord, tailWord_3079151, baseEnd_3079151] using wordTrace_append hprefix tailTrace_3079151
  have hstable : (prefixWord ++ tailWord_3079151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079151).length < 2 ^ (prefixWord ++ tailWord_3079151).sum := by decide
  have hdescent : baseEnd_3079151 < baseStart_3079151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079162 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_3079162 : Nat := 118140960795 + 3079162 * 2 ^ 59
def prefixEnd_3079162 : Nat := 4983230072969 + 3 ^ 40 * 3079162 * 2
def baseEnd_3079162 : Nat := 1054060079373057998809465

theorem tailTrace_3079162 : CollatzResearch.WordTrace tailWord_3079162 prefixEnd_3079162 1054060079373057998809465 := by
  unfold tailWord_3079162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076566117682356961835935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74870842980486285231562493 28076566117682356961835935)
  ·
    refine ⟨42114849176523535442753903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28076566117682356961835935 42114849176523535442753903)
    ·
      refine ⟨63172273764785303164130855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42114849176523535442753903 63172273764785303164130855)
      ·
        refine ⟨94758410647177954746196283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63172273764785303164130855 94758410647177954746196283)
        ·
          refine ⟨142137615970766932119294425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94758410647177954746196283 142137615970766932119294425)
          ·
            refine ⟨106603211978075199089470819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142137615970766932119294425 106603211978075199089470819)
            ·
              refine ⟨159904817967112798634206229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106603211978075199089470819 159904817967112798634206229)
              ·
                refine ⟨7495538342208412435978417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159904817967112798634206229 7495538342208412435978417)
                ·
                  refine ⟨5621653756656309326983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7495538342208412435978417 5621653756656309326983813)
                  ·
                    refine ⟨1054060079373057998809465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5621653756656309326983813 1054060079373057998809465)
                    ·
                      rfl

theorem cell22_3079162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_3079162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079162 prefixEnd_3079162 := by exact prefixLift 3079162
  have htrace : WordTrace (prefixWord ++ tailWord_3079162) baseStart_3079162 baseEnd_3079162 := by
    simpa [prefixWord, tailWord_3079162, baseEnd_3079162] using wordTrace_append hprefix tailTrace_3079162
  have hstable : (prefixWord ++ tailWord_3079162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079162).length < 2 ^ (prefixWord ++ tailWord_3079162).sum := by decide
  have hdescent : baseEnd_3079162 < baseStart_3079162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079164 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_3079164 : Nat := 118140960795 + 3079164 * 2 ^ 59
def prefixEnd_3079164 : Nat := 4983230072969 + 3 ^ 40 * 3079164 * 2
def baseEnd_3079164 : Nat := 1054060764013930660259459

theorem tailTrace_3079164 : CollatzResearch.WordTrace tailWord_3079164 prefixEnd_3079164 1054060764013930660259459 := by
  unfold tailWord_3079164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56153168708361091094458273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74870891611148121459277697 56153168708361091094458273)
  ·
    refine ⟨42114876531270818320843705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56153168708361091094458273 42114876531270818320843705)
    ·
      refine ⟨31586157398453113740632779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42114876531270818320843705 31586157398453113740632779)
      ·
        refine ⟨47379236097679670610949169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31586157398453113740632779 47379236097679670610949169)
        ·
          refine ⟨35534427073259752958211877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47379236097679670610949169 35534427073259752958211877)
          ·
            refine ⟨6662705076236203679664727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35534427073259752958211877 6662705076236203679664727)
            ·
              refine ⟨9994057614354305519497091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662705076236203679664727 9994057614354305519497091)
              ·
                refine ⟨14991086421531458279245637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9994057614354305519497091 14991086421531458279245637)
                ·
                  refine ⟨2810828704037148427358557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14991086421531458279245637 2810828704037148427358557)
                  ·
                    refine ⟨1054060764013930660259459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810828704037148427358557 1054060764013930660259459)
                    ·
                      rfl

theorem cell22_3079164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_3079164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079164 prefixEnd_3079164 := by exact prefixLift 3079164
  have htrace : WordTrace (prefixWord ++ tailWord_3079164) baseStart_3079164 baseEnd_3079164 := by
    simpa [prefixWord, tailWord_3079164, baseEnd_3079164] using wordTrace_append hprefix tailTrace_3079164
  have hstable : (prefixWord ++ tailWord_3079164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079164).length < 2 ^ (prefixWord ++ tailWord_3079164).sum := by decide
  have hdescent : baseEnd_3079164 < baseStart_3079164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079166 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3079166 : Nat := 118140960795 + 3079166 * 2 ^ 59
def prefixEnd_3079166 : Nat := 4983230072969 + 3 ^ 40 * 3079166 * 2
def baseEnd_3079166 : Nat := 351353816218267773903151

theorem tailTrace_3079166 : CollatzResearch.WordTrace tailWord_3079166 prefixEnd_3079166 351353816218267773903151 := by
  unfold tailWord_3079166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14038301295339367066311169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74870940241809957686992901 14038301295339367066311169)
  ·
    refine ⟨10528725971504525299733377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14038301295339367066311169 10528725971504525299733377)
    ·
      refine ⟨7896544478628393974800033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10528725971504525299733377 7896544478628393974800033)
      ·
        refine ⟨5922408358971295481100025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7896544478628393974800033 5922408358971295481100025)
        ·
          refine ⟨4441806269228471610825019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5922408358971295481100025 4441806269228471610825019)
          ·
            refine ⟨6662709403842707416237529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441806269228471610825019 6662709403842707416237529)
            ·
              refine ⟨4997032052882030562178147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6662709403842707416237529 4997032052882030562178147)
              ·
                refine ⟨7495548079323045843267221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997032052882030562178147 7495548079323045843267221)
                ·
                  refine ⟨351353816218267773903151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7495548079323045843267221 351353816218267773903151)
                  ·
                    rfl

theorem cell22_3079166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3079166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079166 prefixEnd_3079166 := by exact prefixLift 3079166
  have htrace : WordTrace (prefixWord ++ tailWord_3079166) baseStart_3079166 baseEnd_3079166 := by
    simpa [prefixWord, tailWord_3079166, baseEnd_3079166] using wordTrace_append hprefix tailTrace_3079166
  have hstable : (prefixWord ++ tailWord_3079166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079166).length < 2 ^ (prefixWord ++ tailWord_3079166).sum := by decide
  have hdescent : baseEnd_3079166 < baseStart_3079166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079200 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_3079200 : Nat := 118140960795 + 3079200 * 2 ^ 59
def prefixEnd_3079200 : Nat := 4983230072969 + 3 ^ 40 * 3079200 * 2
def baseEnd_3079200 : Nat := 351357695849879522119783

theorem tailTrace_3079200 : CollatzResearch.WordTrace tailWord_3079200 prefixEnd_3079200 351357695849879522119783 := by
  unfold tailWord_3079200
  simp only [CollatzResearch.WordTrace]
  refine ⟨56153825222295880168613527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74871766963061173558151369 56153825222295880168613527)
  ·
    refine ⟨84230737833443820252920291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56153825222295880168613527 84230737833443820252920291)
    ·
      refine ⟨126346106750165730379380437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84230737833443820252920291 126346106750165730379380437)
      ·
        refine ⟨2961236876957009305766729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 126346106750165730379380437 2961236876957009305766729)
        ·
          refine ⟨2220927657717756979325047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2961236876957009305766729 2220927657717756979325047)
          ·
            refine ⟨3331391486576635468987571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220927657717756979325047 3331391486576635468987571)
            ·
              refine ⟨4997087229864953203481357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331391486576635468987571 4997087229864953203481357)
              ·
                refine ⟨1873907711199357451305509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4997087229864953203481357 1873907711199357451305509)
                ·
                  refine ⟨351357695849879522119783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873907711199357451305509 351357695849879522119783)
                  ·
                    rfl

theorem cell22_3079200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_3079200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079200 prefixEnd_3079200 := by exact prefixLift 3079200
  have htrace : WordTrace (prefixWord ++ tailWord_3079200) baseStart_3079200 baseEnd_3079200 := by
    simpa [prefixWord, tailWord_3079200, baseEnd_3079200] using wordTrace_append hprefix tailTrace_3079200
  have hstable : (prefixWord ++ tailWord_3079200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079200).length < 2 ^ (prefixWord ++ tailWord_3079200).sum := by decide
  have hdescent : baseEnd_3079200 < baseStart_3079200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079226 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_3079226 : Nat := 118140960795 + 3079226 * 2 ^ 59
def prefixEnd_3079226 : Nat := 4983230072969 + 3 ^ 40 * 3079226 * 2
def baseEnd_3079226 : Nat := 1054081987880983165209269

theorem tailTrace_3079226 : CollatzResearch.WordTrace tailWord_3079226 prefixEnd_3079226 1054081987880983165209269 := by
  unfold tailWord_3079226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28077149685624391694418383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74872399161665044518449021 28077149685624391694418383)
  ·
    refine ⟨42115724528436587541627575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28077149685624391694418383 42115724528436587541627575)
    ·
      refine ⟨63173586792654881312441363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42115724528436587541627575 63173586792654881312441363)
      ·
        refine ⟨94760380188982321968662045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63173586792654881312441363 94760380188982321968662045)
        ·
          refine ⟨35535142570868370738248267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94760380188982321968662045 35535142570868370738248267)
          ·
            refine ⟨53302713856302556107372401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35535142570868370738248267 53302713856302556107372401)
            ·
              refine ⟨39977035392226917080529301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53302713856302556107372401 39977035392226917080529301)
              ·
                refine ⟨1873923534010636738149811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39977035392226917080529301 1873923534010636738149811)
                ·
                  refine ⟨2810885301015955107224717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873923534010636738149811 2810885301015955107224717)
                  ·
                    refine ⟨1054081987880983165209269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810885301015955107224717 1054081987880983165209269)
                    ·
                      rfl

theorem cell22_3079226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_3079226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079226 prefixEnd_3079226 := by exact prefixLift 3079226
  have htrace : WordTrace (prefixWord ++ tailWord_3079226) baseStart_3079226 baseEnd_3079226 := by
    simpa [prefixWord, tailWord_3079226, baseEnd_3079226] using wordTrace_append hprefix tailTrace_3079226
  have hstable : (prefixWord ++ tailWord_3079226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079226).length < 2 ^ (prefixWord ++ tailWord_3079226).sum := by decide
  have hdescent : baseEnd_3079226 < baseStart_3079226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079237 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_3079237 : Nat := 118140960795 + 3079237 * 2 ^ 59
def prefixEnd_3079237 : Nat := 4983230072969 + 3 ^ 40 * 3079237 * 2
def baseEnd_3079237 : Nat := 1054085753405782803184235

theorem tailTrace_3079237 : CollatzResearch.WordTrace tailWord_3079237 prefixEnd_3079237 1054085753405782803184235 := by
  unfold tailWord_3079237
  simp only [CollatzResearch.WordTrace]
  refine ⟨112308999945457715656323965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74872666630305143770882643 112308999945457715656323965)
  ·
    refine ⟨42115874979546643371121487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112308999945457715656323965 42115874979546643371121487)
    ·
      refine ⟨63173812469319965056682231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42115874979546643371121487 63173812469319965056682231)
      ·
        refine ⟨94760718703979947585023347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63173812469319965056682231 94760718703979947585023347)
        ·
          refine ⟨142141078055969921377535021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94760718703979947585023347 142141078055969921377535021)
          ·
            refine ⟨53302904270988720516575633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142141078055969921377535021 53302904270988720516575633)
            ·
              refine ⟨39977178203241540387431725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53302904270988720516575633 39977178203241540387431725)
              ·
                refine ⟨14991441826215577645286897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39977178203241540387431725 14991441826215577645286897)
                ·
                  refine ⟨11243581369661683233965173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14991441826215577645286897 11243581369661683233965173)
                  ·
                    refine ⟨1054085753405782803184235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11243581369661683233965173 1054085753405782803184235)
                    ·
                      rfl

theorem cell22_3079237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_3079237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079237 prefixEnd_3079237 := by exact prefixLift 3079237
  have htrace : WordTrace (prefixWord ++ tailWord_3079237) baseStart_3079237 baseEnd_3079237 := by
    simpa [prefixWord, tailWord_3079237, baseEnd_3079237] using wordTrace_append hprefix tailTrace_3079237
  have hstable : (prefixWord ++ tailWord_3079237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079237).length < 2 ^ (prefixWord ++ tailWord_3079237).sum := by decide
  have hdescent : baseEnd_3079237 < baseStart_3079237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079239 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 5]
def baseStart_3079239 : Nat := 118140960795 + 3079239 * 2 ^ 59
def prefixEnd_3079239 : Nat := 4983230072969 + 3 ^ 40 * 3079239 * 2
def baseEnd_3079239 : Nat := 351362146015551821544743

theorem tailTrace_3079239 : CollatzResearch.WordTrace tailWord_3079239 prefixEnd_3079239 351362146015551821544743 := by
  unfold tailWord_3079239
  simp only [CollatzResearch.WordTrace]
  refine ⟨112309072891450469997896771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74872715260966979998597847 112309072891450469997896771)
  ·
    refine ⟨168463609337175704996845157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112309072891450469997896771 168463609337175704996845157)
    ·
      refine ⟨31586926750720444686908467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168463609337175704996845157 31586926750720444686908467)
      ·
        refine ⟨47380390126080667030362701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31586926750720444686908467 47380390126080667030362701)
        ·
          refine ⟨17767646297280250136386013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47380390126080667030362701 17767646297280250136386013)
          ·
            refine ⟨6662867361480093801144755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17767646297280250136386013 6662867361480093801144755)
            ·
              refine ⟨9994301042220140701717133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662867361480093801144755 9994301042220140701717133)
              ·
                refine ⟨3747862890832552763143925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9994301042220140701717133 3747862890832552763143925)
                ·
                  refine ⟨351362146015551821544743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3747862890832552763143925 351362146015551821544743)
                  ·
                    rfl

theorem cell22_3079239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 5].length) (baseStart_3079239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079239 prefixEnd_3079239 := by exact prefixLift 3079239
  have htrace : WordTrace (prefixWord ++ tailWord_3079239) baseStart_3079239 baseEnd_3079239 := by
    simpa [prefixWord, tailWord_3079239, baseEnd_3079239] using wordTrace_append hprefix tailTrace_3079239
  have hstable : (prefixWord ++ tailWord_3079239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079239).length < 2 ^ (prefixWord ++ tailWord_3079239).sum := by decide
  have hdescent : baseEnd_3079239 < baseStart_3079239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079299 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 1, 5]
def baseStart_3079299 : Nat := 118140960795 + 3079299 * 2 ^ 59
def prefixEnd_3079299 : Nat := 4983230072969 + 3 ^ 40 * 3079299 * 2
def baseEnd_3079299 : Nat := 1054106977272835308134045

theorem tailTrace_3079299 : CollatzResearch.WordTrace tailWord_3079299 prefixEnd_3079299 1054106977272835308134045 := by
  unfold tailWord_3079299
  simp only [CollatzResearch.WordTrace]
  refine ⟨112311261271233100245080951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74874174180822066830053967 112311261271233100245080951)
  ·
    refine ⟨168466891906849650367621427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112311261271233100245080951 168466891906849650367621427)
    ·
      refine ⟨252700337860274475551432141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168466891906849650367621427 252700337860274475551432141)
      ·
        refine ⟨94762626697602928331787053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252700337860274475551432141 94762626697602928331787053)
        ·
          refine ⟨35535985011601098124420145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94762626697602928331787053 35535985011601098124420145)
          ·
            refine ⟨26651988758700823593315109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35535985011601098124420145 26651988758700823593315109)
            ·
              refine ⟨4997247892256404423746583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26651988758700823593315109 4997247892256404423746583)
              ·
                refine ⟨7495871838384606635619875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997247892256404423746583 7495871838384606635619875)
                ·
                  refine ⟨11243807757576909953429813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495871838384606635619875 11243807757576909953429813)
                  ·
                    refine ⟨1054106977272835308134045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11243807757576909953429813 1054106977272835308134045)
                    ·
                      rfl

theorem cell22_3079299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_3079299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079299 prefixEnd_3079299 := by exact prefixLift 3079299
  have htrace : WordTrace (prefixWord ++ tailWord_3079299) baseStart_3079299 baseEnd_3079299 := by
    simpa [prefixWord, tailWord_3079299, baseEnd_3079299] using wordTrace_append hprefix tailTrace_3079299
  have hstable : (prefixWord ++ tailWord_3079299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079299).length < 2 ^ (prefixWord ++ tailWord_3079299).sum := by decide
  have hdescent : baseEnd_3079299 < baseStart_3079299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079333 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_3079333 : Nat := 118140960795 + 3079333 * 2 ^ 59
def prefixEnd_3079333 : Nat := 4983230072969 + 3 ^ 40 * 3079333 * 2
def baseEnd_3079333 : Nat := 1054118616167670552783941

theorem tailTrace_3079333 : CollatzResearch.WordTrace tailWord_3079333 prefixEnd_3079333 1054118616167670552783941 := by
  unfold tailWord_3079333
  simp only [CollatzResearch.WordTrace]
  refine ⟨112312501353109924051818653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74875000902073282701212435 112312501353109924051818653)
  ·
    refine ⟨42117188007416221519431995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112312501353109924051818653 42117188007416221519431995)
    ·
      refine ⟨63175782011124332279147993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42117188007416221519431995 63175782011124332279147993)
      ·
        refine ⟨47381836508343249209360995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63175782011124332279147993 47381836508343249209360995)
        ·
          refine ⟨71072754762514873814041493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47381836508343249209360995 71072754762514873814041493)
          ·
            refine ⟨3331535379492884710033195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71072754762514873814041493 3331535379492884710033195)
            ·
              refine ⟨4997303069239327065049793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331535379492884710033195 4997303069239327065049793)
              ·
                refine ⟨3747977301929495298787345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4997303069239327065049793 3747977301929495298787345)
                ·
                  refine ⟨2810982976447121474090509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747977301929495298787345 2810982976447121474090509)
                  ·
                    refine ⟨1054118616167670552783941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810982976447121474090509 1054118616167670552783941)
                    ·
                      rfl

theorem cell22_3079333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_3079333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079333 prefixEnd_3079333 := by exact prefixLift 3079333
  have htrace : WordTrace (prefixWord ++ tailWord_3079333) baseStart_3079333 baseEnd_3079333 := by
    simpa [prefixWord, tailWord_3079333, baseEnd_3079333] using wordTrace_append hprefix tailTrace_3079333
  have hstable : (prefixWord ++ tailWord_3079333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079333).length < 2 ^ (prefixWord ++ tailWord_3079333).sum := by decide
  have hdescent : baseEnd_3079333 < baseStart_3079333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079344 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_3079344 : Nat := 118140960795 + 3079344 * 2 ^ 59
def prefixEnd_3079344 : Nat := 4983230072969 + 3 ^ 40 * 3079344 * 2
def baseEnd_3079344 : Nat := 1054122381692470190758907

theorem tailTrace_3079344 : CollatzResearch.WordTrace tailWord_3079344 prefixEnd_3079344 1054122381692470190758907 := by
  unfold tailWord_3079344
  simp only [CollatzResearch.WordTrace]
  refine ⟨56156451278035036465234543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74875268370713381953646057 56156451278035036465234543)
  ·
    refine ⟨84234676917052554697851815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56156451278035036465234543 84234676917052554697851815)
    ·
      refine ⟨126352015375578832046777723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84234676917052554697851815 126352015375578832046777723)
      ·
        refine ⟨189528023063368248070166585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126352015375578832046777723 189528023063368248070166585)
        ·
          refine ⟨142146017297526186052624939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189528023063368248070166585 142146017297526186052624939)
          ·
            refine ⟨213219025946289279078937409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142146017297526186052624939 213219025946289279078937409)
            ·
              refine ⟨159914269459716959309203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213219025946289279078937409 159914269459716959309203057)
              ·
                refine ⟨119935702094787719481902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159914269459716959309203057 119935702094787719481902293)
                ·
                  refine ⟨2810993017846587175357085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119935702094787719481902293 2810993017846587175357085)
                  ·
                    refine ⟨1054122381692470190758907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810993017846587175357085 1054122381692470190758907)
                    ·
                      rfl

theorem cell22_3079344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_3079344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079344 prefixEnd_3079344 := by exact prefixLift 3079344
  have htrace : WordTrace (prefixWord ++ tailWord_3079344) baseStart_3079344 baseEnd_3079344 := by
    simpa [prefixWord, tailWord_3079344, baseEnd_3079344] using wordTrace_append hprefix tailTrace_3079344
  have hstable : (prefixWord ++ tailWord_3079344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079344).length < 2 ^ (prefixWord ++ tailWord_3079344).sum := by decide
  have hdescent : baseEnd_3079344 < baseStart_3079344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079496 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_3079496 : Nat := 118140960795 + 3079496 * 2 ^ 59
def prefixEnd_3079496 : Nat := 4983230072969 + 3 ^ 40 * 3079496 * 2
def baseEnd_3079496 : Nat := 1054174414398792460958441

theorem tailTrace_3079496 : CollatzResearch.WordTrace tailWord_3079496 prefixEnd_3079496 1054174414398792460958441 := by
  unfold tailWord_3079496
  simp only [CollatzResearch.WordTrace]
  refine ⟨56159223225759701445001171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74878964301012935260001561 56159223225759701445001171)
  ·
    refine ⟨84238834838639552167501757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56159223225759701445001171 84238834838639552167501757)
    ·
      refine ⟨31589563064489832062813159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84238834838639552167501757 31589563064489832062813159)
      ·
        refine ⟨47384344596734748094219739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31589563064489832062813159 47384344596734748094219739)
        ·
          refine ⟨71076516895102122141329609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47384344596734748094219739 71076516895102122141329609)
          ·
            refine ⟨53307387671326591605997207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71076516895102122141329609 53307387671326591605997207)
            ·
              refine ⟨79961081506989887408995811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53307387671326591605997207 79961081506989887408995811)
              ·
                refine ⟨119941622260484831113493717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79961081506989887408995811 119941622260484831113493717)
                ·
                  refine ⟨2811131771730113229222509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119941622260484831113493717 2811131771730113229222509)
                  ·
                    refine ⟨1054174414398792460958441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811131771730113229222509 1054174414398792460958441)
                    ·
                      rfl

theorem cell22_3079496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_3079496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079496 prefixEnd_3079496 := by exact prefixLift 3079496
  have htrace : WordTrace (prefixWord ++ tailWord_3079496) baseStart_3079496 baseEnd_3079496 := by
    simpa [prefixWord, tailWord_3079496, baseEnd_3079496] using wordTrace_append hprefix tailTrace_3079496
  have hstable : (prefixWord ++ tailWord_3079496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079496).length < 2 ^ (prefixWord ++ tailWord_3079496).sum := by decide
  have hdescent : baseEnd_3079496 < baseStart_3079496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079682 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3079682 : Nat := 118140960795 + 3079682 * 2 ^ 59
def prefixEnd_3079682 : Nat := 4983230072969 + 3 ^ 40 * 3079682 * 2
def baseEnd_3079682 : Nat := 1054238085999949975807871

theorem tailTrace_3079682 : CollatzResearch.WordTrace tailWord_3079682 prefixEnd_3079682 1054238085999949975807871 := by
  unfold tailWord_3079682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081307607211389164068325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74883486952563704437515533 28081307607211389164068325)
  ·
    refine ⟨5265245176352135468262811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28081307607211389164068325 5265245176352135468262811)
    ·
      refine ⟨7897867764528203202394217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5265245176352135468262811 7897867764528203202394217)
      ·
        refine ⟨5923400823396152401795663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7897867764528203202394217 5923400823396152401795663)
        ·
          refine ⟨8885101235094228602693495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923400823396152401795663 8885101235094228602693495)
          ·
            refine ⟨13327651852641342904040243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8885101235094228602693495 13327651852641342904040243)
            ·
              refine ⟨19991477778962014356060365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13327651852641342904040243 19991477778962014356060365)
              ·
                refine ⟨7496804167110755383522637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19991477778962014356060365 7496804167110755383522637)
                ·
                  refine ⟨2811301562666533268820989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7496804167110755383522637 2811301562666533268820989)
                  ·
                    refine ⟨1054238085999949975807871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811301562666533268820989 1054238085999949975807871)
                    ·
                      rfl

theorem cell22_3079682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3079682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079682 prefixEnd_3079682 := by exact prefixLift 3079682
  have htrace : WordTrace (prefixWord ++ tailWord_3079682) baseStart_3079682 baseEnd_3079682 := by
    simpa [prefixWord, tailWord_3079682, baseEnd_3079682] using wordTrace_append hprefix tailTrace_3079682
  have hstable : (prefixWord ++ tailWord_3079682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079682).length < 2 ^ (prefixWord ++ tailWord_3079682).sum := by decide
  have hdescent : baseEnd_3079682 < baseStart_3079682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079789 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3079789 : Nat := 118140960795 + 3079789 * 2 ^ 59
def prefixEnd_3079789 : Nat := 4983230072969 + 3 ^ 40 * 3079789 * 2
def baseEnd_3079789 : Nat := 1054274714286637363382543

theorem tailTrace_3079789 : CollatzResearch.WordTrace tailWord_3079789 prefixEnd_3079789 1054274714286637363382543 := by
  unfold tailWord_3079789
  simp only [CollatzResearch.WordTrace]
  refine ⟨112329133039457913930418421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74886088692971942620278947 112329133039457913930418421)
  ·
    refine ⟨10530856222449179430976727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112329133039457913930418421 10530856222449179430976727)
    ·
      refine ⟨15796284333673769146465091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10530856222449179430976727 15796284333673769146465091)
      ·
        refine ⟨23694426500510653719697637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15796284333673769146465091 23694426500510653719697637)
        ·
          refine ⟨4442704968845747572443307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23694426500510653719697637 4442704968845747572443307)
          ·
            refine ⟨6664057453268621358664961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442704968845747572443307 6664057453268621358664961)
            ·
              refine ⟨4998043089951466018998721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664057453268621358664961 4998043089951466018998721)
              ·
                refine ⟨3748532317463599514249041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998043089951466018998721 3748532317463599514249041)
                ·
                  refine ⟨2811399238097699635686781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3748532317463599514249041 2811399238097699635686781)
                  ·
                    refine ⟨1054274714286637363382543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811399238097699635686781 1054274714286637363382543)
                    ·
                      rfl

theorem cell22_3079789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3079789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079789 prefixEnd_3079789 := by exact prefixLift 3079789
  have htrace : WordTrace (prefixWord ++ tailWord_3079789) baseStart_3079789 baseEnd_3079789 := by
    simpa [prefixWord, tailWord_3079789, baseEnd_3079789] using wordTrace_append hprefix tailTrace_3079789
  have hstable : (prefixWord ++ tailWord_3079789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079789).length < 2 ^ (prefixWord ++ tailWord_3079789).sum := by decide
  have hdescent : baseEnd_3079789 < baseStart_3079789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079909 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 4]
def baseStart_3079909 : Nat := 118140960795 + 3079909 * 2 ^ 59
def prefixEnd_3079909 : Nat := 4983230072969 + 3 ^ 40 * 3079909 * 2
def baseEnd_3079909 : Nat := 351438597579665683460725

theorem tailTrace_3079909 : CollatzResearch.WordTrace tailWord_3079909 prefixEnd_3079909 351438597579665683460725 := by
  unfold tailWord_3079909
  simp only [CollatzResearch.WordTrace]
  refine ⟨112333509799023174424786781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74889006532682116283191187 112333509799023174424786781)
  ·
    refine ⟨42125066174633690409295043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112333509799023174424786781 42125066174633690409295043)
    ·
      refine ⟨63187599261950535613942565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42125066174633690409295043 63187599261950535613942565)
      ·
        refine ⟨11847674861615725427614231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63187599261950535613942565 11847674861615725427614231)
        ·
          refine ⟨17771512292423588141421347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847674861615725427614231 17771512292423588141421347)
          ·
            refine ⟨26657268438635382212132021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17771512292423588141421347 26657268438635382212132021)
            ·
              refine ⟨2499118916122067082387377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26657268438635382212132021 2499118916122067082387377)
              ·
                refine ⟨1874339187091550311790533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499118916122067082387377 1874339187091550311790533)
                ·
                  refine ⟨351438597579665683460725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874339187091550311790533 351438597579665683460725)
                  ·
                    rfl

theorem cell22_3079909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_3079909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079909 prefixEnd_3079909 := by exact prefixLift 3079909
  have htrace : WordTrace (prefixWord ++ tailWord_3079909) baseStart_3079909 baseEnd_3079909 := by
    simpa [prefixWord, tailWord_3079909, baseEnd_3079909] using wordTrace_append hprefix tailTrace_3079909
  have hstable : (prefixWord ++ tailWord_3079909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079909).length < 2 ^ (prefixWord ++ tailWord_3079909).sum := by decide
  have hdescent : baseEnd_3079909 < baseStart_3079909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079980 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_3079980 : Nat := 118140960795 + 3079980 * 2 ^ 59
def prefixEnd_3079980 : Nat := 4983230072969 + 3 ^ 40 * 3079980 * 2
def baseEnd_3079980 : Nat := 1054340097489976531856957

theorem tailTrace_3079980 : CollatzResearch.WordTrace tailWord_3079980 prefixEnd_3079980 1054340097489976531856957 := by
  unfold tailWord_3079980
  simp only [CollatzResearch.WordTrace]
  refine ⟨56168049690882976775310697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74890732921177302367080929 56168049690882976775310697)
  ·
    refine ⟨42126037268162232581483023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56168049690882976775310697 42126037268162232581483023)
    ·
      refine ⟨63189055902243348872224535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42126037268162232581483023 63189055902243348872224535)
      ·
        refine ⟨94783583853365023308336803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63189055902243348872224535 94783583853365023308336803)
        ·
          refine ⟨142175375780047534962505205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94783583853365023308336803 142175375780047534962505205)
          ·
            refine ⟨13328941479379456402734863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142175375780047534962505205 13328941479379456402734863)
            ·
              refine ⟨19993412219069184604102295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13328941479379456402734863 19993412219069184604102295)
              ·
                refine ⟨29990118328603776906153443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19993412219069184604102295 29990118328603776906153443)
                ·
                  refine ⟨44985177492905665359230165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29990118328603776906153443 44985177492905665359230165)
                  ·
                    refine ⟨1054340097489976531856957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44985177492905665359230165 1054340097489976531856957)
                    ·
                      rfl

theorem cell22_3079980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_3079980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3079980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3079980 prefixEnd_3079980 := by exact prefixLift 3079980
  have htrace : WordTrace (prefixWord ++ tailWord_3079980) baseStart_3079980 baseEnd_3079980 := by
    simpa [prefixWord, tailWord_3079980, baseEnd_3079980] using wordTrace_append hprefix tailTrace_3079980
  have hstable : (prefixWord ++ tailWord_3079980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079980).length < 2 ^ (prefixWord ++ tailWord_3079980).sum := by decide
  have hdescent : baseEnd_3079980 < baseStart_3079980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080010 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_3080010 : Nat := 118140960795 + 3080010 * 2 ^ 59
def prefixEnd_3080010 : Nat := 4983230072969 + 3 ^ 40 * 3080010 * 2
def baseEnd_3080010 : Nat := 351450122367688817868955

theorem tailTrace_3080010 : CollatzResearch.WordTrace tailWord_3080010 prefixEnd_3080010 351450122367688817868955 := by
  unfold tailWord_3080010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28084298392914317168553371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74891462381104845782808989 28084298392914317168553371)
  ·
    refine ⟨42126447589371475752830057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28084298392914317168553371 42126447589371475752830057)
    ·
      refine ⟨31594835692028606814622543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42126447589371475752830057 31594835692028606814622543)
      ·
        refine ⟨47392253538042910221933815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31594835692028606814622543 47392253538042910221933815)
        ·
          refine ⟨71088380307064365332900723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47392253538042910221933815 71088380307064365332900723)
          ·
            refine ⟨106632570460596547999351085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71088380307064365332900723 106632570460596547999351085)
            ·
              refine ⟨39987213922723705499756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106632570460596547999351085 39987213922723705499756657)
              ·
                refine ⟨29990410442042779124817493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39987213922723705499756657 29990410442042779124817493)
                ·
                  refine ⟨351450122367688817868955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29990410442042779124817493 351450122367688817868955)
                  ·
                    rfl

theorem cell22_3080010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_3080010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080010 prefixEnd_3080010 := by exact prefixLift 3080010
  have htrace : WordTrace (prefixWord ++ tailWord_3080010) baseStart_3080010 baseEnd_3080010 := by
    simpa [prefixWord, tailWord_3080010, baseEnd_3080010] using wordTrace_append hprefix tailTrace_3080010
  have hstable : (prefixWord ++ tailWord_3080010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080010).length < 2 ^ (prefixWord ++ tailWord_3080010).sum := by decide
  have hdescent : baseEnd_3080010 < baseStart_3080010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080046 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3080046 : Nat := 118140960795 + 3080046 * 2 ^ 59
def prefixEnd_3080046 : Nat := 4983230072969 + 3 ^ 40 * 3080046 * 2
def baseEnd_3080046 : Nat := 1054362690638774359706755

theorem tailTrace_3080046 : CollatzResearch.WordTrace tailWord_3080046 prefixEnd_3080046 1054362690638774359706755 := by
  unfold tailWord_3080046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14042313324940855852815499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74892337733017897881682661 14042313324940855852815499)
  ·
    refine ⟨21063469987411283779223249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14042313324940855852815499 21063469987411283779223249)
    ·
      refine ⟨15797602490558462834417437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21063469987411283779223249 15797602490558462834417437)
      ·
        refine ⟨5924100933959423562906539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15797602490558462834417437 5924100933959423562906539)
        ·
          refine ⟨8886151400939135344359809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924100933959423562906539 8886151400939135344359809)
          ·
            refine ⟨6664613550704351508269857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8886151400939135344359809 6664613550704351508269857)
            ·
              refine ⟨4998460163028263631202393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664613550704351508269857 4998460163028263631202393)
              ·
                refine ⟨3748845122271197723401795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998460163028263631202393 3748845122271197723401795)
                ·
                  refine ⟨5623267683406796585102693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748845122271197723401795 5623267683406796585102693)
                  ·
                    refine ⟨1054362690638774359706755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623267683406796585102693 1054362690638774359706755)
                    ·
                      rfl

theorem cell22_3080046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3080046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080046 prefixEnd_3080046 := by exact prefixLift 3080046
  have htrace : WordTrace (prefixWord ++ tailWord_3080046) baseStart_3080046 baseEnd_3080046 := by
    simpa [prefixWord, tailWord_3080046, baseEnd_3080046] using wordTrace_append hprefix tailTrace_3080046
  have hstable : (prefixWord ++ tailWord_3080046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080046).length < 2 ^ (prefixWord ++ tailWord_3080046).sum := by decide
  have hdescent : baseEnd_3080046 < baseStart_3080046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080057 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_3080057 : Nat := 118140960795 + 3080057 * 2 ^ 59
def prefixEnd_3080057 : Nat := 4983230072969 + 3 ^ 40 * 3080057 * 2
def baseEnd_3080057 : Nat := 1054366456163573997681721

theorem tailTrace_3080057 : CollatzResearch.WordTrace tailWord_3080057 prefixEnd_3080057 1054366456163573997681721 := by
  unfold tailWord_3080057
  simp only [CollatzResearch.WordTrace]
  refine ⟨112338907802486995701174425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74892605201657997134116283 112338907802486995701174425)
  ·
    refine ⟨84254180851865246775880819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112338907802486995701174425 84254180851865246775880819)
    ·
      refine ⟨126381271277797870163821229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84254180851865246775880819 126381271277797870163821229)
      ·
        refine ⟨47392976729174201311432961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126381271277797870163821229 47392976729174201311432961)
        ·
          refine ⟨35544732546880650983574721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47392976729174201311432961 35544732546880650983574721)
          ·
            refine ⟨26658549410160488237681041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35544732546880650983574721 26658549410160488237681041)
            ·
              refine ⟨19993912057620366178260781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26658549410160488237681041 19993912057620366178260781)
              ·
                refine ⟨7497717021607637316847793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19993912057620366178260781 7497717021607637316847793)
                ·
                  refine ⟨5623287766205727987635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7497717021607637316847793 5623287766205727987635845)
                  ·
                    refine ⟨1054366456163573997681721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623287766205727987635845 1054366456163573997681721)
                    ·
                      rfl

theorem cell22_3080057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_3080057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080057 prefixEnd_3080057 := by exact prefixLift 3080057
  have htrace : WordTrace (prefixWord ++ tailWord_3080057) baseStart_3080057 baseEnd_3080057 := by
    simpa [prefixWord, tailWord_3080057, baseEnd_3080057] using wordTrace_append hprefix tailTrace_3080057
  have hstable : (prefixWord ++ tailWord_3080057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080057).length < 2 ^ (prefixWord ++ tailWord_3080057).sum := by decide
  have hdescent : baseEnd_3080057 < baseStart_3080057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080078 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_3080078 : Nat := 118140960795 + 3080078 * 2 ^ 59
def prefixEnd_3080078 : Nat := 4983230072969 + 3 ^ 40 * 3080078 * 2
def baseEnd_3080078 : Nat := 351457881630912314302219

theorem tailTrace_3080078 : CollatzResearch.WordTrace tailWord_3080078 prefixEnd_3080078 351457881630912314302219 := by
  unfold tailWord_3080078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14042459216926364535961111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74893115823607277525125925 14042459216926364535961111)
  ·
    refine ⟨21063688825389546803941667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14042459216926364535961111 21063688825389546803941667)
    ·
      refine ⟨31595533238084320205912501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21063688825389546803941667 31595533238084320205912501)
      ·
        refine ⟨2962081241070405019304297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31595533238084320205912501 2962081241070405019304297)
        ·
          refine ⟨2221560930802803764478223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962081241070405019304297 2221560930802803764478223)
          ·
            refine ⟨3332341396204205646717335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221560930802803764478223 3332341396204205646717335)
            ·
              refine ⟨4998512094306308470076003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332341396204205646717335 4998512094306308470076003)
              ·
                refine ⟨7497768141459462705114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998512094306308470076003 7497768141459462705114005)
                ·
                  refine ⟨351457881630912314302219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7497768141459462705114005 351457881630912314302219)
                  ·
                    rfl

theorem cell22_3080078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_3080078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080078 prefixEnd_3080078 := by exact prefixLift 3080078
  have htrace : WordTrace (prefixWord ++ tailWord_3080078) baseStart_3080078 baseEnd_3080078 := by
    simpa [prefixWord, tailWord_3080078, baseEnd_3080078] using wordTrace_append hprefix tailTrace_3080078
  have hstable : (prefixWord ++ tailWord_3080078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080078).length < 2 ^ (prefixWord ++ tailWord_3080078).sum := by decide
  have hdescent : baseEnd_3080078 < baseStart_3080078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080093 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3080093 : Nat := 118140960795 + 3080093 * 2 ^ 59
def prefixEnd_3080093 : Nat := 4983230072969 + 3 ^ 40 * 3080093 * 2
def baseEnd_3080093 : Nat := 1054378779699281903781611

theorem tailTrace_3080093 : CollatzResearch.WordTrace tailWord_3080093 prefixEnd_3080093 1054378779699281903781611 := by
  unfold tailWord_3080093
  simp only [CollatzResearch.WordTrace]
  refine ⟨112340220830356573849484933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74893480553571049232989955 112340220830356573849484933)
  ·
    refine ⟨21063791405691857596778425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112340220830356573849484933 21063791405691857596778425)
    ·
      refine ⟨15797843554268893197583819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21063791405691857596778425 15797843554268893197583819)
      ·
        refine ⟨23696765331403339796375729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15797843554268893197583819 23696765331403339796375729)
        ·
          refine ⟨17772573998552504847281797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23696765331403339796375729 17772573998552504847281797)
          ·
            refine ⟨3332357624728594658865337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17772573998552504847281797 3332357624728594658865337)
            ·
              refine ⟨2499268218546445994149003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332357624728594658865337 2499268218546445994149003)
              ·
                refine ⟨3748902327819668991223505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499268218546445994149003 3748902327819668991223505)
                ·
                  refine ⟨2811676745864751743417629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3748902327819668991223505 2811676745864751743417629)
                  ·
                    refine ⟨1054378779699281903781611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811676745864751743417629 1054378779699281903781611)
                    ·
                      rfl

theorem cell22_3080093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3080093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080093 prefixEnd_3080093 := by exact prefixLift 3080093
  have htrace : WordTrace (prefixWord ++ tailWord_3080093) baseStart_3080093 baseEnd_3080093 := by
    simpa [prefixWord, tailWord_3080093, baseEnd_3080093] using wordTrace_append hprefix tailTrace_3080093
  have hstable : (prefixWord ++ tailWord_3080093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080093).length < 2 ^ (prefixWord ++ tailWord_3080093).sum := by decide
  have hdescent : baseEnd_3080093 < baseStart_3080093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080121 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 1, 3]
def baseStart_3080121 : Nat := 118140960795 + 3080121 * 2 ^ 59
def prefixEnd_3080121 : Nat := 4983230072969 + 3 ^ 40 * 3080121 * 2
def baseEnd_3080121 : Nat := 1054388364671499164081525

theorem tailTrace_3080121 : CollatzResearch.WordTrace tailWord_3080121 prefixEnd_3080121 1054388364671499164081525 := by
  unfold tailWord_3080121
  simp only [CollatzResearch.WordTrace]
  refine ⟨112341242074255134631504217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74894161382836756421002811 112341242074255134631504217)
  ·
    refine ⟨84255931555691350973628163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112341242074255134631504217 84255931555691350973628163)
    ·
      refine ⟨126383897333537026460442245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84255931555691350973628163 126383897333537026460442245)
      ·
        refine ⟨23696980750038192461332921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126383897333537026460442245 23696980750038192461332921)
        ·
          refine ⟨17772735562528644345999691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23696980750038192461332921 17772735562528644345999691)
          ·
            refine ⟨26659103343792966518999537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17772735562528644345999691 26659103343792966518999537)
            ·
              refine ⟨19994327507844724889249653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26659103343792966518999537 19994327507844724889249653)
              ·
                refine ⟨1874468203860442958367155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19994327507844724889249653 1874468203860442958367155)
                ·
                  refine ⟨2811702305790664437550733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874468203860442958367155 2811702305790664437550733)
                  ·
                    refine ⟨1054388364671499164081525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811702305790664437550733 1054388364671499164081525)
                    ·
                      rfl

theorem cell22_3080121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_3080121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080121 prefixEnd_3080121 := by exact prefixLift 3080121
  have htrace : WordTrace (prefixWord ++ tailWord_3080121) baseStart_3080121 baseEnd_3080121 := by
    simpa [prefixWord, tailWord_3080121, baseEnd_3080121] using wordTrace_append hprefix tailTrace_3080121
  have hstable : (prefixWord ++ tailWord_3080121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080121).length < 2 ^ (prefixWord ++ tailWord_3080121).sum := by decide
  have hdescent : baseEnd_3080121 < baseStart_3080121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080138 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3080138 : Nat := 118140960795 + 3080138 * 2 ^ 59
def prefixEnd_3080138 : Nat := 4983230072969 + 3 ^ 40 * 3080138 * 2
def baseEnd_3080138 : Nat := 1054394184118916786406473

theorem tailTrace_3080138 : CollatzResearch.WordTrace tailWord_3080138 prefixEnd_3080138 1054394184118916786406473 := by
  unfold tailWord_3080138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085465528798386633718267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74894574743462364356582045 28085465528798386633718267)
  ·
    refine ⟨42128198293197579950577401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28085465528798386633718267 42128198293197579950577401)
    ·
      refine ⟨31596148719898184962933051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42128198293197579950577401 31596148719898184962933051)
      ·
        refine ⟨47394223079847277444399577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31596148719898184962933051 47394223079847277444399577)
        ·
          refine ⟨35545667309885458083299683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47394223079847277444399577 35545667309885458083299683)
          ·
            refine ⟨53318500964828187124949525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35545667309885458083299683 53318500964828187124949525)
            ·
              refine ⟨2499304732726321271482009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53318500964828187124949525 2499304732726321271482009)
              ·
                refine ⟨1874478549544740953611507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499304732726321271482009 1874478549544740953611507)
                ·
                  refine ⟨2811717824317111430417261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874478549544740953611507 2811717824317111430417261)
                  ·
                    refine ⟨1054394184118916786406473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811717824317111430417261 1054394184118916786406473)
                    ·
                      rfl

theorem cell22_3080138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3080138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080138 prefixEnd_3080138 := by exact prefixLift 3080138
  have htrace : WordTrace (prefixWord ++ tailWord_3080138) baseStart_3080138 baseEnd_3080138 := by
    simpa [prefixWord, tailWord_3080138, baseEnd_3080138] using wordTrace_append hprefix tailTrace_3080138
  have hstable : (prefixWord ++ tailWord_3080138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080138).length < 2 ^ (prefixWord ++ tailWord_3080138).sum := by decide
  have hdescent : baseEnd_3080138 < baseStart_3080138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080149 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3080149 : Nat := 118140960795 + 3080149 * 2 ^ 59
def prefixEnd_3080149 : Nat := 4983230072969 + 3 ^ 40 * 3080149 * 2
def baseEnd_3080149 : Nat := 1054397949643716424381439

theorem tailTrace_3080149 : CollatzResearch.WordTrace tailWord_3080149 prefixEnd_3080149 1054397949643716424381439 := by
  unfold tailWord_3080149
  simp only [CollatzResearch.WordTrace]
  refine ⟨112342263318153695413523501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74894842212102463609015667 112342263318153695413523501)
  ·
    refine ⟨42128348744307635780071313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112342263318153695413523501 42128348744307635780071313)
    ·
      refine ⟨31596261558230726835053485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42128348744307635780071313 31596261558230726835053485)
      ·
        refine ⟨11848598084336522563145057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31596261558230726835053485 11848598084336522563145057)
        ·
          refine ⟨8886448563252391922358793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11848598084336522563145057 8886448563252391922358793)
          ·
            refine ⟨6664836422439293941769095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8886448563252391922358793 6664836422439293941769095)
            ·
              refine ⟨9997254633658940912653643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6664836422439293941769095 9997254633658940912653643)
              ·
                refine ⟨14995881950488411368980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9997254633658940912653643 14995881950488411368980465)
                ·
                  refine ⟨11246911462866308526735349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14995881950488411368980465 11246911462866308526735349)
                  ·
                    refine ⟨1054397949643716424381439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11246911462866308526735349 1054397949643716424381439)
                    ·
                      rfl

theorem cell22_3080149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3080149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080149 prefixEnd_3080149 := by exact prefixLift 3080149
  have htrace : WordTrace (prefixWord ++ tailWord_3080149) baseStart_3080149 baseEnd_3080149 := by
    simpa [prefixWord, tailWord_3080149, baseEnd_3080149] using wordTrace_append hprefix tailTrace_3080149
  have hstable : (prefixWord ++ tailWord_3080149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080149).length < 2 ^ (prefixWord ++ tailWord_3080149).sum := by decide
  have hdescent : baseEnd_3080149 < baseStart_3080149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080164 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_3080164 : Nat := 118140960795 + 3080164 * 2 ^ 59
def prefixEnd_3080164 : Nat := 4983230072969 + 3 ^ 40 * 3080164 * 2
def baseEnd_3080164 : Nat := 1054403084450261385256393

theorem tailTrace_3080164 : CollatzResearch.WordTrace tailWord_3080164 prefixEnd_3080164 1054403084450261385256393 := by
  unfold tailWord_3080164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56171405206549676487659773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74895206942066235316879697 56171405206549676487659773)
  ·
    refine ⟨21064276952456128682872415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56171405206549676487659773 21064276952456128682872415)
    ·
      refine ⟨31596415428684193024308623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21064276952456128682872415 31596415428684193024308623)
      ·
        refine ⟨47394623143026289536462935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31596415428684193024308623 47394623143026289536462935)
        ·
          refine ⟨71091934714539434304694403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47394623143026289536462935 71091934714539434304694403)
          ·
            refine ⟨106637902071809151457041605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71091934714539434304694403 106637902071809151457041605)
            ·
              refine ⟨19994606638464215898195301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106637902071809151457041605 19994606638464215898195301)
              ·
                refine ⟨3748988744712040480911619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19994606638464215898195301 3748988744712040480911619)
                ·
                  refine ⟨5623483117068060721367429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748988744712040480911619 5623483117068060721367429)
                  ·
                    refine ⟨1054403084450261385256393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623483117068060721367429 1054403084450261385256393)
                    ·
                      rfl

theorem cell22_3080164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_3080164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080164 prefixEnd_3080164 := by exact prefixLift 3080164
  have htrace : WordTrace (prefixWord ++ tailWord_3080164) baseStart_3080164 baseEnd_3080164 := by
    simpa [prefixWord, tailWord_3080164, baseEnd_3080164] using wordTrace_append hprefix tailTrace_3080164
  have hstable : (prefixWord ++ tailWord_3080164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080164).length < 2 ^ (prefixWord ++ tailWord_3080164).sum := by decide
  have hdescent : baseEnd_3080164 < baseStart_3080164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080256 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_3080256 : Nat := 118140960795 + 3080256 * 2 ^ 59
def prefixEnd_3080256 : Nat := 4983230072969 + 3 ^ 40 * 3080256 * 2
def baseEnd_3080256 : Nat := 1054434577930403811956111

theorem tailTrace_3080256 : CollatzResearch.WordTrace tailWord_3080256 prefixEnd_3080256 1054434577930403811956111 := by
  unfold tailWord_3080256
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173082964383026343834311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74897443952510701791779081 56173082964383026343834311)
  ·
    refine ⟨84259624446574539515751467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56173082964383026343834311 84259624446574539515751467)
    ·
      refine ⟨126389436669861809273627201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84259624446574539515751467 126389436669861809273627201)
      ·
        refine ⟨94792077502396356955220401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126389436669861809273627201 94792077502396356955220401)
        ·
          refine ⟨71094058126797267716415301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94792077502396356955220401 71094058126797267716415301)
          ·
            refine ⟨13330135898774487696827869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71094058126797267716415301 13330135898774487696827869)
            ·
              refine ⟨4998800962040432886310451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13330135898774487696827869 4998800962040432886310451)
              ·
                refine ⟨7498201443060649329465677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998800962040432886310451 7498201443060649329465677)
                ·
                  refine ⟨2811825541147743498549629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7498201443060649329465677 2811825541147743498549629)
                  ·
                    refine ⟨1054434577930403811956111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811825541147743498549629 1054434577930403811956111)
                    ·
                      rfl

theorem cell22_3080256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_3080256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080256 prefixEnd_3080256 := by exact prefixLift 3080256
  have htrace : WordTrace (prefixWord ++ tailWord_3080256) baseStart_3080256 baseEnd_3080256 := by
    simpa [prefixWord, tailWord_3080256, baseEnd_3080256] using wordTrace_append hprefix tailTrace_3080256
  have hstable : (prefixWord ++ tailWord_3080256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080256).length < 2 ^ (prefixWord ++ tailWord_3080256).sum := by decide
  have hdescent : baseEnd_3080256 < baseStart_3080256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080348 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_3080348 : Nat := 118140960795 + 3080348 * 2 ^ 59
def prefixEnd_3080348 : Nat := 4983230072969 + 3 ^ 40 * 3080348 * 2
def baseEnd_3080348 : Nat := 351488690470182079551943

theorem tailTrace_3080348 : CollatzResearch.WordTrace tailWord_3080348 prefixEnd_3080348 351488690470182079551943 := by
  unfold tailWord_3080348
  simp only [CollatzResearch.WordTrace]
  refine ⟨56174760722216376200008849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74899680962955168266678465 56174760722216376200008849)
  ·
    refine ⟨42131070541662282150006637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56174760722216376200008849 42131070541662282150006637)
    ·
      refine ⟨15799151453123355806252489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42131070541662282150006637 15799151453123355806252489)
      ·
        refine ⟨11849363589842516854689367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15799151453123355806252489 11849363589842516854689367)
        ·
          refine ⟨17774045384763775282034051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849363589842516854689367 17774045384763775282034051)
          ·
            refine ⟨26661068077145662923051077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774045384763775282034051 26661068077145662923051077)
            ·
              refine ⟨4998950264464811798072077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26661068077145662923051077 4998950264464811798072077)
              ·
                refine ⟨1874606349174304424277029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4998950264464811798072077 1874606349174304424277029)
                ·
                  refine ⟨351488690470182079551943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874606349174304424277029 351488690470182079551943)
                  ·
                    rfl

theorem cell22_3080348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_3080348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080348 prefixEnd_3080348 := by exact prefixLift 3080348
  have htrace : WordTrace (prefixWord ++ tailWord_3080348) baseStart_3080348 baseEnd_3080348 := by
    simpa [prefixWord, tailWord_3080348, baseEnd_3080348] using wordTrace_append hprefix tailTrace_3080348
  have hstable : (prefixWord ++ tailWord_3080348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080348).length < 2 ^ (prefixWord ++ tailWord_3080348).sum := by decide
  have hdescent : baseEnd_3080348 < baseStart_3080348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080350 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3080350 : Nat := 118140960795 + 3080350 * 2 ^ 59
def prefixEnd_3080350 : Nat := 4983230072969 + 3 ^ 40 * 3080350 * 2
def baseEnd_3080350 : Nat := 1054466756051418900105823

theorem tailTrace_3080350 : CollatzResearch.WordTrace tailWord_3080350 prefixEnd_3080350 1054466756051418900105823 := by
  unfold tailWord_3080350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14043699298803188342698813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74899729593617004494393669 14043699298803188342698813)
  ·
    refine ⟨5266387237051195628512055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14043699298803188342698813 5266387237051195628512055)
    ·
      refine ⟨7899580855576793442768083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266387237051195628512055 7899580855576793442768083)
      ·
        refine ⟨11849371283365190164152125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899580855576793442768083 11849371283365190164152125)
        ·
          refine ⟨4443514231261946311557047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11849371283365190164152125 4443514231261946311557047)
          ·
            refine ⟨6665271346892919467335571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443514231261946311557047 6665271346892919467335571)
            ·
              refine ⟨9997907020339379201003357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665271346892919467335571 9997907020339379201003357)
              ·
                refine ⟨3749215132627267200376259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9997907020339379201003357 3749215132627267200376259)
                ·
                  refine ⟨5623822698940900800564389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749215132627267200376259 5623822698940900800564389)
                  ·
                    refine ⟨1054466756051418900105823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5623822698940900800564389 1054466756051418900105823)
                    ·
                      rfl

theorem cell22_3080350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3080350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080350 prefixEnd_3080350 := by exact prefixLift 3080350
  have htrace : WordTrace (prefixWord ++ tailWord_3080350) baseStart_3080350 baseEnd_3080350 := by
    simpa [prefixWord, tailWord_3080350, baseEnd_3080350] using wordTrace_append hprefix tailTrace_3080350
  have hstable : (prefixWord ++ tailWord_3080350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080350).length < 2 ^ (prefixWord ++ tailWord_3080350).sum := by decide
  have hdescent : baseEnd_3080350 < baseStart_3080350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080380 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_3080380 : Nat := 118140960795 + 3080380 * 2 ^ 59
def prefixEnd_3080380 : Nat := 4983230072969 + 3 ^ 40 * 3080380 * 2
def baseEnd_3080380 : Nat := 1054477025664508821855731

theorem tailTrace_3080380 : CollatzResearch.WordTrace tailWord_3080380 prefixEnd_3080380 1054477025664508821855731 := by
  unfold tailWord_3080380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56175344290158410932591297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74900459053544547910121729 56175344290158410932591297)
  ·
    refine ⟨42131508217618808199443473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56175344290158410932591297 42131508217618808199443473)
    ·
      refine ⟨31598631163214106149582605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42131508217618808199443473 31598631163214106149582605)
      ·
        refine ⟨11849486686205289806093477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31598631163214106149582605 11849486686205289806093477)
        ·
          refine ⟨2221778753663491838642527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11849486686205289806093477 2221778753663491838642527)
          ·
            refine ⟨3332668130495237757963791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221778753663491838642527 3332668130495237757963791)
            ·
              refine ⟨4999002195742856636945687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332668130495237757963791 4999002195742856636945687)
              ·
                refine ⟨7498503293614284955418531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999002195742856636945687 7498503293614284955418531)
                ·
                  refine ⟨11247754940421427433127797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498503293614284955418531 11247754940421427433127797)
                  ·
                    refine ⟨1054477025664508821855731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11247754940421427433127797 1054477025664508821855731)
                    ·
                      rfl

theorem cell22_3080380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_3080380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080380 prefixEnd_3080380 := by exact prefixLift 3080380
  have htrace : WordTrace (prefixWord ++ tailWord_3080380) baseStart_3080380 baseEnd_3080380 := by
    simpa [prefixWord, tailWord_3080380, baseEnd_3080380] using wordTrace_append hprefix tailTrace_3080380
  have hstable : (prefixWord ++ tailWord_3080380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080380).length < 2 ^ (prefixWord ++ tailWord_3080380).sum := by decide
  have hdescent : baseEnd_3080380 < baseStart_3080380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080389 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_3080389 : Nat := 118140960795 + 3080389 * 2 ^ 59
def prefixEnd_3080389 : Nat := 4983230072969 + 3 ^ 40 * 3080389 * 2
def baseEnd_3080389 : Nat := 1054480106548435798380703

theorem tailTrace_3080389 : CollatzResearch.WordTrace tailWord_3080389 prefixEnd_3080389 1054480106548435798380703 := by
  unfold tailWord_3080389
  simp only [CollatzResearch.WordTrace]
  refine ⟨112351016837284216402260221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74900677891522810934840147 112351016837284216402260221)
  ·
    refine ⟨42131631313981581150847583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112351016837284216402260221 42131631313981581150847583)
    ·
      refine ⟨63197446970972371726271375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42131631313981581150847583 63197446970972371726271375)
      ·
        refine ⟨94796170456458557589407063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63197446970972371726271375 94796170456458557589407063)
        ·
          refine ⟨142194255684687836384110595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94796170456458557589407063 142194255684687836384110595)
          ·
            refine ⟨213291383527031754576165893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142194255684687836384110595 213291383527031754576165893)
            ·
              refine ⟨39992134411318453983031105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213291383527031754576165893 39992134411318453983031105)
              ·
                refine ⟨29994100808488840487273329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39992134411318453983031105 29994100808488840487273329)
                ·
                  refine ⟨22495575606366630365454997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29994100808488840487273329 22495575606366630365454997)
                  ·
                    refine ⟨1054480106548435798380703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22495575606366630365454997 1054480106548435798380703)
                    ·
                      rfl

theorem cell22_3080389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_3080389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080389 prefixEnd_3080389 := by exact prefixLift 3080389
  have htrace : WordTrace (prefixWord ++ tailWord_3080389) baseStart_3080389 baseEnd_3080389 := by
    simpa [prefixWord, tailWord_3080389, baseEnd_3080389] using wordTrace_append hprefix tailTrace_3080389
  have hstable : (prefixWord ++ tailWord_3080389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080389).length < 2 ^ (prefixWord ++ tailWord_3080389).sum := by decide
  have hdescent : baseEnd_3080389 < baseStart_3080389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080421 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 7]
def baseStart_3080421 : Nat := 118140960795 + 3080421 * 2 ^ 59
def prefixEnd_3080421 : Nat := 4983230072969 + 3 ^ 40 * 3080421 * 2
def baseEnd_3080421 : Nat := 351497020267466127193535

theorem tailTrace_3080421 : CollatzResearch.WordTrace tailWord_3080421 prefixEnd_3080421 351497020267466127193535 := by
  unfold tailWord_3080421
  simp only [CollatzResearch.WordTrace]
  refine ⟨112352183973168285867425117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74901455982112190578283411 112352183973168285867425117)
  ·
    refine ⟨42132068989938107200284419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112352183973168285867425117 42132068989938107200284419)
    ·
      refine ⟨63198103484907160800426629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42132068989938107200284419 63198103484907160800426629)
      ·
        refine ⟨11849644403420092650079993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63198103484907160800426629 11849644403420092650079993)
        ·
          refine ⟨8887233302565069487559995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11849644403420092650079993 8887233302565069487559995)
          ·
            refine ⟨13330849953847604231339993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887233302565069487559995 13330849953847604231339993)
            ·
              refine ⟨9998137465385703173504995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13330849953847604231339993 9998137465385703173504995)
              ·
                refine ⟨14997206198078554760257493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998137465385703173504995 14997206198078554760257493)
                ·
                  refine ⟨351497020267466127193535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14997206198078554760257493 351497020267466127193535)
                  ·
                    rfl

theorem cell22_3080421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_3080421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080421 prefixEnd_3080421 := by exact prefixLift 3080421
  have htrace : WordTrace (prefixWord ++ tailWord_3080421) baseStart_3080421 baseEnd_3080421 := by
    simpa [prefixWord, tailWord_3080421, baseEnd_3080421] using wordTrace_append hprefix tailTrace_3080421
  have hstable : (prefixWord ++ tailWord_3080421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080421).length < 2 ^ (prefixWord ++ tailWord_3080421).sum := by decide
  have hdescent : baseEnd_3080421 < baseStart_3080421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080451 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_3080451 : Nat := 118140960795 + 3080451 * 2 ^ 59
def prefixEnd_3080451 : Nat := 4983230072969 + 3 ^ 40 * 3080451 * 2
def baseEnd_3080451 : Nat := 1054501330415488303330513

theorem tailTrace_3080451 : CollatzResearch.WordTrace tailWord_3080451 prefixEnd_3080451 1054501330415488303330513 := by
  unfold tailWord_3080451
  simp only [CollatzResearch.WordTrace]
  refine ⟨112353278163059600991017207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74902185442039733994011471 112353278163059600991017207)
  ·
    refine ⟨168529917244589401486525811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112353278163059600991017207 168529917244589401486525811)
    ·
      refine ⟨252794875866884102229788717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168529917244589401486525811 252794875866884102229788717)
      ·
        refine ⟨94798078450081538336170769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252794875866884102229788717 94798078450081538336170769)
        ·
          refine ⟨71098558837561153752128077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94798078450081538336170769 71098558837561153752128077)
          ·
            refine ⟨26661959564085432657048029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71098558837561153752128077 26661959564085432657048029)
            ·
              refine ⟨9998234836532037246393011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26661959564085432657048029 9998234836532037246393011)
              ·
                refine ⟨14997352254798055869589517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998234836532037246393011 14997352254798055869589517)
                ·
                  refine ⟨5624007095549270951096069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14997352254798055869589517 5624007095549270951096069)
                  ·
                    refine ⟨1054501330415488303330513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624007095549270951096069 1054501330415488303330513)
                    ·
                      rfl

theorem cell22_3080451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_3080451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080451 prefixEnd_3080451 := by exact prefixLift 3080451
  have htrace : WordTrace (prefixWord ++ tailWord_3080451) baseStart_3080451 baseEnd_3080451 := by
    simpa [prefixWord, tailWord_3080451, baseEnd_3080451] using wordTrace_append hprefix tailTrace_3080451
  have hstable : (prefixWord ++ tailWord_3080451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080451).length < 2 ^ (prefixWord ++ tailWord_3080451).sum := by decide
  have hdescent : baseEnd_3080451 < baseStart_3080451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080483 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 4]
def baseStart_3080483 : Nat := 118140960795 + 3080483 * 2 ^ 59
def prefixEnd_3080483 : Nat := 4983230072969 + 3 ^ 40 * 3080483 * 2
def baseEnd_3080483 : Nat := 351504094889816962176805

theorem tailTrace_3080483 : CollatzResearch.WordTrace tailWord_3080483 prefixEnd_3080483 351504094889816962176805 := by
  unfold tailWord_3080483
  simp only [CollatzResearch.WordTrace]
  refine ⟨112354445298943670456182103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74902963532629113637454735 112354445298943670456182103)
  ·
    refine ⟨168531667948415505684273155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112354445298943670456182103 168531667948415505684273155)
    ·
      refine ⟨252797501922623258526409733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168531667948415505684273155 252797501922623258526409733)
      ·
        refine ⟨47399531610491860973701825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252797501922623258526409733 47399531610491860973701825)
        ·
          refine ⟨35549648707868895730276369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47399531610491860973701825 35549648707868895730276369)
          ·
            refine ⟨26662236530901671797707277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35549648707868895730276369 26662236530901671797707277)
            ·
              refine ⟨9998338699088126924140229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26662236530901671797707277 9998338699088126924140229)
              ·
                refine ⟨1874688506079023798276293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9998338699088126924140229 1874688506079023798276293)
                ·
                  refine ⟨351504094889816962176805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874688506079023798276293 351504094889816962176805)
                  ·
                    rfl

theorem cell22_3080483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 4].length) (baseStart_3080483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080483 prefixEnd_3080483 := by exact prefixLift 3080483
  have htrace : WordTrace (prefixWord ++ tailWord_3080483) baseStart_3080483 baseEnd_3080483 := by
    simpa [prefixWord, tailWord_3080483, baseEnd_3080483] using wordTrace_append hprefix tailTrace_3080483
  have hstable : (prefixWord ++ tailWord_3080483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080483).length < 2 ^ (prefixWord ++ tailWord_3080483).sum := by decide
  have hdescent : baseEnd_3080483 < baseStart_3080483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080487 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3080487 : Nat := 118140960795 + 3080487 * 2 ^ 59
def prefixEnd_3080487 : Nat := 4983230072969 + 3 ^ 40 * 3080487 * 2
def baseEnd_3080487 : Nat := 1054513653951196209430403

theorem tailTrace_3080487 : CollatzResearch.WordTrace tailWord_3080487 prefixEnd_3080487 1054513653951196209430403 := by
  unfold tailWord_3080487
  simp only [CollatzResearch.WordTrace]
  refine ⟨112354591190929179139327715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74903060793952786092885143 112354591190929179139327715)
  ·
    refine ⟨168531886786393768708991573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112354591190929179139327715 168531886786393768708991573)
    ·
      refine ⟨1974983048278051977058495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 168531886786393768708991573 1974983048278051977058495)
      ·
        refine ⟨2962474572417077965587743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974983048278051977058495 2962474572417077965587743)
        ·
          refine ⟨4443711858625616948381615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962474572417077965587743 4443711858625616948381615)
          ·
            refine ⟨6665567787938425422572423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443711858625616948381615 6665567787938425422572423)
            ·
              refine ⟨9998351681907638133858635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665567787938425422572423 9998351681907638133858635)
              ·
                refine ⟨14997527522861457200787953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998351681907638133858635 14997527522861457200787953)
                ·
                  refine ⟨11248145642146092900590965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14997527522861457200787953 11248145642146092900590965)
                  ·
                    refine ⟨1054513653951196209430403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11248145642146092900590965 1054513653951196209430403)
                    ·
                      rfl

theorem cell22_3080487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3080487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080487 prefixEnd_3080487 := by exact prefixLift 3080487
  have htrace : WordTrace (prefixWord ++ tailWord_3080487) baseStart_3080487 baseEnd_3080487 := by
    simpa [prefixWord, tailWord_3080487, baseEnd_3080487] using wordTrace_append hprefix tailTrace_3080487
  have hstable : (prefixWord ++ tailWord_3080487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080487).length < 2 ^ (prefixWord ++ tailWord_3080487).sum := by decide
  have hdescent : baseEnd_3080487 < baseStart_3080487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080532 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3080532 : Nat := 118140960795 + 3080532 * 2 ^ 59
def prefixEnd_3080532 : Nat := 4983230072969 + 3 ^ 40 * 3080532 * 2
def baseEnd_3080532 : Nat := 1054529058370831092055265

theorem tailTrace_3080532 : CollatzResearch.WordTrace tailWord_3080532 prefixEnd_3080532 1054529058370831092055265 := by
  unfold tailWord_3080532
  simp only [CollatzResearch.WordTrace]
  refine ⟨56178116237883075912357925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74904154983844101216477233 56178116237883075912357925)
  ·
    refine ⟨10533396794603076733567111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56178116237883075912357925 10533396794603076733567111)
    ·
      refine ⟨15800095191904615100350667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10533396794603076733567111 15800095191904615100350667)
      ·
        refine ⟨23700142787856922650526001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15800095191904615100350667 23700142787856922650526001)
        ·
          refine ⟨17775107090892691987894501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23700142787856922650526001 17775107090892691987894501)
          ·
            refine ⟨3332832579542379747730219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17775107090892691987894501 3332832579542379747730219)
            ·
              refine ⟨4999248869313569621595329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332832579542379747730219 4999248869313569621595329)
              ·
                refine ⟨3749436651985177216196497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999248869313569621595329 3749436651985177216196497)
                ·
                  refine ⟨2812077488988882912147373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3749436651985177216196497 2812077488988882912147373)
                  ·
                    refine ⟨1054529058370831092055265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812077488988882912147373 1054529058370831092055265)
                    ·
                      rfl

theorem cell22_3080532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3080532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080532 prefixEnd_3080532 := by exact prefixLift 3080532
  have htrace : WordTrace (prefixWord ++ tailWord_3080532) baseStart_3080532 baseEnd_3080532 := by
    simpa [prefixWord, tailWord_3080532, baseEnd_3080532] using wordTrace_append hprefix tailTrace_3080532
  have hstable : (prefixWord ++ tailWord_3080532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080532).length < 2 ^ (prefixWord ++ tailWord_3080532).sum := by decide
  have hdescent : baseEnd_3080532 < baseStart_3080532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080543 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 3, 3]
def baseStart_3080543 : Nat := 118140960795 + 3080543 * 2 ^ 59
def prefixEnd_3080543 : Nat := 4983230072969 + 3 ^ 40 * 3080543 * 2
def baseEnd_3080543 : Nat := 1054532823895630730030231

theorem tailTrace_3080543 : CollatzResearch.WordTrace tailWord_3080543 prefixEnd_3080543 1054532823895630730030231 := by
  unfold tailWord_3080543
  simp only [CollatzResearch.WordTrace]
  refine ⟨112356633678726300703366283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74904422452484200468910855 112356633678726300703366283)
  ·
    refine ⟨168534950518089451055049425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112356633678726300703366283 168534950518089451055049425)
    ·
      refine ⟨126401212888567088291287069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168534950518089451055049425 126401212888567088291287069)
      ·
        refine ⟨47400454833212658109232651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126401212888567088291287069 47400454833212658109232651)
        ·
          refine ⟨71100682249818987163848977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47400454833212658109232651 71100682249818987163848977)
          ·
            refine ⟨53325511687364240372886733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71100682249818987163848977 53325511687364240372886733)
            ·
              refine ⟨19997066882761590139832525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53325511687364240372886733 19997066882761590139832525)
              ·
                refine ⟨7498900081035596302437197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19997066882761590139832525 7498900081035596302437197)
                ·
                  refine ⟨2812087530388348613413949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7498900081035596302437197 2812087530388348613413949)
                  ·
                    refine ⟨1054532823895630730030231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812087530388348613413949 1054532823895630730030231)
                    ·
                      rfl

theorem cell22_3080543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_3080543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080543 prefixEnd_3080543 := by exact prefixLift 3080543
  have htrace : WordTrace (prefixWord ++ tailWord_3080543) baseStart_3080543 baseEnd_3080543 := by
    simpa [prefixWord, tailWord_3080543, baseEnd_3080543] using wordTrace_append hprefix tailTrace_3080543
  have hstable : (prefixWord ++ tailWord_3080543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080543).length < 2 ^ (prefixWord ++ tailWord_3080543).sum := by decide
  have hdescent : baseEnd_3080543 < baseStart_3080543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080633 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_3080633 : Nat := 118140960795 + 3080633 * 2 ^ 59
def prefixEnd_3080633 : Nat := 4983230072969 + 3 ^ 40 * 3080633 * 2
def baseEnd_3080633 : Nat := 1054563632734900495279955

theorem tailTrace_3080633 : CollatzResearch.WordTrace tailWord_3080633 prefixEnd_3080633 1054563632734900495279955 := by
  unfold tailWord_3080633
  simp only [CollatzResearch.WordTrace]
  refine ⟨112359916248400246074142553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74906610832266830716095035 112359916248400246074142553)
  ·
    refine ⟨84269937186300184555606915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112359916248400246074142553 84269937186300184555606915)
    ·
      refine ⟨126404905779450276833410373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84269937186300184555606915 126404905779450276833410373)
      ·
        refine ⟨23700919833646926906264445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126404905779450276833410373 23700919833646926906264445)
        ·
          refine ⟨8887844937617597589849167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23700919833646926906264445 8887844937617597589849167)
          ·
            refine ⟨13331767406426396384773751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887844937617597589849167 13331767406426396384773751)
            ·
              refine ⟨19997651109639594577160627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13331767406426396384773751 19997651109639594577160627)
              ·
                refine ⟨29996476664459391865740941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19997651109639594577160627 29996476664459391865740941)
                ·
                  refine ⟨11248678749172271949652853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29996476664459391865740941 11248678749172271949652853)
                  ·
                    refine ⟨1054563632734900495279955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11248678749172271949652853 1054563632734900495279955)
                    ·
                      rfl

theorem cell22_3080633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_3080633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080633 prefixEnd_3080633 := by exact prefixLift 3080633
  have htrace : WordTrace (prefixWord ++ tailWord_3080633) baseStart_3080633 baseEnd_3080633 := by
    simpa [prefixWord, tailWord_3080633, baseEnd_3080633] using wordTrace_append hprefix tailTrace_3080633
  have hstable : (prefixWord ++ tailWord_3080633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080633).length < 2 ^ (prefixWord ++ tailWord_3080633).sum := by decide
  have hdescent : baseEnd_3080633 < baseStart_3080633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080637 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_3080637 : Nat := 118140960795 + 3080637 * 2 ^ 59
def prefixEnd_3080637 : Nat := 4983230072969 + 3 ^ 40 * 3080637 * 2
def baseEnd_3080637 : Nat := 1054565002016645818179943

theorem tailTrace_3080637 : CollatzResearch.WordTrace tailWord_3080637 prefixEnd_3080637 1054565002016645818179943 := by
  unfold tailWord_3080637
  simp only [CollatzResearch.WordTrace]
  refine ⟨112360062140385754757288165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74906708093590503171525443 112360062140385754757288165)
  ·
    refine ⟨21067511651322329016991531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112360062140385754757288165 21067511651322329016991531)
    ·
      refine ⟨31601267476983493525487297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21067511651322329016991531 31601267476983493525487297)
      ·
        refine ⟨23700950607737620144115473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31601267476983493525487297 23700950607737620144115473)
        ·
          refine ⟨17775712955803215108086605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23700950607737620144115473 17775712955803215108086605)
          ·
            refine ⟨6665892358426205665532477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17775712955803215108086605 6665892358426205665532477)
            ·
              refine ⟨2499709634409827124574679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6665892358426205665532477 2499709634409827124574679)
              ·
                refine ⟨3749564451614740686862019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499709634409827124574679 3749564451614740686862019)
                ·
                  refine ⟨5624346677422111030293029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749564451614740686862019 5624346677422111030293029)
                  ·
                    refine ⟨1054565002016645818179943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624346677422111030293029 1054565002016645818179943)
                    ·
                      rfl

theorem cell22_3080637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_3080637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080637 prefixEnd_3080637 := by exact prefixLift 3080637
  have htrace : WordTrace (prefixWord ++ tailWord_3080637) baseStart_3080637 baseEnd_3080637 := by
    simpa [prefixWord, tailWord_3080637, baseEnd_3080637] using wordTrace_append hprefix tailTrace_3080637
  have hstable : (prefixWord ++ tailWord_3080637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080637).length < 2 ^ (prefixWord ++ tailWord_3080637).sum := by decide
  have hdescent : baseEnd_3080637 < baseStart_3080637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080652 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_3080652 : Nat := 118140960795 + 3080652 * 2 ^ 59
def prefixEnd_3080652 : Nat := 4983230072969 + 3 ^ 40 * 3080652 * 2
def baseEnd_3080652 : Nat := 351523378941063593018299

theorem tailTrace_3080652 : CollatzResearch.WordTrace tailWord_3080652 prefixEnd_3080652 351523378941063593018299 := by
  unfold tailWord_3080652
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180304617665706159542105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74907072823554274879389473 56180304617665706159542105)
  ·
    refine ⟨42135228463249279619656579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56180304617665706159542105 42135228463249279619656579)
    ·
      refine ⟨63202842694873919429484869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42135228463249279619656579 63202842694873919429484869)
      ·
        refine ⟨11850533005288859893028413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63202842694873919429484869 11850533005288859893028413)
        ·
          refine ⟨4443949876983322459885655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11850533005288859893028413 4443949876983322459885655)
          ·
            refine ⟨6665924815474983689828483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443949876983322459885655 6665924815474983689828483)
            ·
              refine ⟨9998887223212475534742725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665924815474983689828483 9998887223212475534742725)
              ·
                refine ⟨1874791354352339162764261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9998887223212475534742725 1874791354352339162764261)
                ·
                  refine ⟨351523378941063593018299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874791354352339162764261 351523378941063593018299)
                  ·
                    rfl

theorem cell22_3080652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_3080652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080652 prefixEnd_3080652 := by exact prefixLift 3080652
  have htrace : WordTrace (prefixWord ++ tailWord_3080652) baseStart_3080652 baseEnd_3080652 := by
    simpa [prefixWord, tailWord_3080652, baseEnd_3080652] using wordTrace_append hprefix tailTrace_3080652
  have hstable : (prefixWord ++ tailWord_3080652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080652).length < 2 ^ (prefixWord ++ tailWord_3080652).sum := by decide
  have hdescent : baseEnd_3080652 < baseStart_3080652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080680 : List Nat := [2, 1, 4, 1, 1, 4, 3, 6]
def baseStart_3080680 : Nat := 118140960795 + 3080680 * 2 ^ 59
def prefixEnd_3080680 : Nat := 4983230072969 + 3 ^ 40 * 3080680 * 2
def baseEnd_3080680 : Nat := 117175524643934226594979

theorem tailTrace_3080680 : CollatzResearch.WordTrace tailWord_3080680 prefixEnd_3080680 117175524643934226594979 := by
  unfold tailWord_3080680
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180815239614986550551747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74907753652819982067402329 56180815239614986550551747)
  ·
    refine ⟨84271222859422479825827621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56180815239614986550551747 84271222859422479825827621)
    ·
      refine ⟨15800854286141714967342679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84271222859422479825827621 15800854286141714967342679)
      ·
        refine ⟨23701281429212572451014019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15800854286141714967342679 23701281429212572451014019)
        ·
          refine ⟨35551922143818858676521029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23701281429212572451014019 35551922143818858676521029)
          ·
            refine ⟨6665985401966036001847693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35551922143818858676521029 6665985401966036001847693)
            ·
              refine ⟨2499744525737263500692885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6665985401966036001847693 2499744525737263500692885)
              ·
                refine ⟨117175524643934226594979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2499744525737263500692885 117175524643934226594979)
                ·
                  rfl

theorem cell22_3080680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_3080680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080680 prefixEnd_3080680 := by exact prefixLift 3080680
  have htrace : WordTrace (prefixWord ++ tailWord_3080680) baseStart_3080680 baseEnd_3080680 := by
    simpa [prefixWord, tailWord_3080680, baseEnd_3080680] using wordTrace_append hprefix tailTrace_3080680
  have hstable : (prefixWord ++ tailWord_3080680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080680).length < 2 ^ (prefixWord ++ tailWord_3080680).sum := by decide
  have hdescent : baseEnd_3080680 < baseStart_3080680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080682 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3080682 : Nat := 118140960795 + 3080682 * 2 ^ 59
def prefixEnd_3080682 : Nat := 4983230072969 + 3 ^ 40 * 3080682 * 2
def baseEnd_3080682 : Nat := 1054580406436280700804805

theorem tailTrace_3080682 : CollatzResearch.WordTrace tailWord_3080682 prefixEnd_3080682 1054580406436280700804805 := by
  unfold tailWord_3080682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28090425856305681860669075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74907802283481818295117533 28090425856305681860669075)
  ·
    refine ⟨42135638784458522791003613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28090425856305681860669075 42135638784458522791003613)
    ·
      refine ⟨15800864544171946046626355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42135638784458522791003613 15800864544171946046626355)
      ·
        refine ⟨23701296816257919069939533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15800864544171946046626355 23701296816257919069939533)
        ·
          refine ⟨8887986306096719651227325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23701296816257919069939533 8887986306096719651227325)
          ·
            refine ⟨3332994864786269869210247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8887986306096719651227325 3332994864786269869210247)
            ·
              refine ⟨4999492297179404803815371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332994864786269869210247 4999492297179404803815371)
              ·
                refine ⟨7499238445769107205723057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999492297179404803815371 7499238445769107205723057)
                ·
                  refine ⟨5624428834326830404292293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7499238445769107205723057 5624428834326830404292293)
                  ·
                    refine ⟨1054580406436280700804805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624428834326830404292293 1054580406436280700804805)
                    ·
                      rfl

theorem cell22_3080682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3080682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080682 prefixEnd_3080682 := by exact prefixLift 3080682
  have htrace : WordTrace (prefixWord ++ tailWord_3080682) baseStart_3080682 baseEnd_3080682 := by
    simpa [prefixWord, tailWord_3080682, baseEnd_3080682] using wordTrace_append hprefix tailTrace_3080682
  have hstable : (prefixWord ++ tailWord_3080682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080682).length < 2 ^ (prefixWord ++ tailWord_3080682).sum := by decide
  have hdescent : baseEnd_3080682 < baseStart_3080682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080723 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_3080723 : Nat := 118140960795 + 3080723 * 2 ^ 59
def prefixEnd_3080723 : Nat := 4983230072969 + 3 ^ 40 * 3080723 * 2
def baseEnd_3080723 : Nat := 1054594441574170260529679

theorem tailTrace_3080723 : CollatzResearch.WordTrace tailWord_3080723 prefixEnd_3080723 1054594441574170260529679 := by
  unfold tailWord_3080723
  simp only [CollatzResearch.WordTrace]
  refine ⟨112363198818074191444918823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74908799212049460963279215 112363198818074191444918823)
  ·
    refine ⟨168544798227111287167378235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112363198818074191444918823 168544798227111287167378235)
    ·
      refine ⟨252817197340666930751067353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168544798227111287167378235 252817197340666930751067353)
      ·
        refine ⟨189612898005500198063300515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252817197340666930751067353 189612898005500198063300515)
        ·
          refine ⟨284419347008250297094950773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189612898005500198063300515 284419347008250297094950773)
          ·
            refine ⟨26664313782023465352651635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284419347008250297094950773 26664313782023465352651635)
            ·
              refine ⟨39996470673035198028977453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26664313782023465352651635 39996470673035198028977453)
              ·
                refine ⟨14998676502388199260866545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39996470673035198028977453 14998676502388199260866545)
                ·
                  refine ⟨11249007376791149445649909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14998676502388199260866545 11249007376791149445649909)
                  ·
                    refine ⟨1054594441574170260529679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11249007376791149445649909 1054594441574170260529679)
                    ·
                      rfl

theorem cell22_3080723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_3080723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080723 prefixEnd_3080723 := by exact prefixLift 3080723
  have htrace : WordTrace (prefixWord ++ tailWord_3080723) baseStart_3080723 baseEnd_3080723 := by
    simpa [prefixWord, tailWord_3080723, baseEnd_3080723] using wordTrace_append hprefix tailTrace_3080723
  have hstable : (prefixWord ++ tailWord_3080723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080723).length < 2 ^ (prefixWord ++ tailWord_3080723).sum := by decide
  have hdescent : baseEnd_3080723 < baseStart_3080723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080746 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3080746 : Nat := 118140960795 + 3080746 * 2 ^ 59
def prefixEnd_3080746 : Nat := 4983230072969 + 3 ^ 40 * 3080746 * 2
def baseEnd_3080746 : Nat := 1054602314944205867204609

theorem tailTrace_3080746 : CollatzResearch.WordTrace tailWord_3080746 prefixEnd_3080746 1054602314944205867204609 := by
  unfold tailWord_3080746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28091009424247716593251523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74909358464660577582004061 28091009424247716593251523)
  ·
    refine ⟨42136514136371574889877285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28091009424247716593251523 42136514136371574889877285)
    ·
      refine ⟨7900596400569670291851991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42136514136371574889877285 7900596400569670291851991)
      ·
        refine ⟨11850894600854505437777987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7900596400569670291851991 11850894600854505437777987)
        ·
          refine ⟨17776341901281758156666981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850894600854505437777987 17776341901281758156666981)
          ·
            refine ⟨3333064106490329654375059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17776341901281758156666981 3333064106490329654375059)
            ·
              refine ⟨4999596159735494481562589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333064106490329654375059 4999596159735494481562589)
              ·
                refine ⟨1874848559900810430585971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4999596159735494481562589 1874848559900810430585971)
                ·
                  refine ⟨2812272839851215645878957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874848559900810430585971 2812272839851215645878957)
                  ·
                    refine ⟨1054602314944205867204609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812272839851215645878957 1054602314944205867204609)
                    ·
                      rfl

theorem cell22_3080746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3080746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080746 prefixEnd_3080746 := by exact prefixLift 3080746
  have htrace : WordTrace (prefixWord ++ tailWord_3080746) baseStart_3080746 baseEnd_3080746 := by
    simpa [prefixWord, tailWord_3080746, baseEnd_3080746] using wordTrace_append hprefix tailTrace_3080746
  have hstable : (prefixWord ++ tailWord_3080746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080746).length < 2 ^ (prefixWord ++ tailWord_3080746).sum := by decide
  have hdescent : baseEnd_3080746 < baseStart_3080746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080753 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 8]
def baseStart_3080753 : Nat := 118140960795 + 3080753 * 2 ^ 59
def prefixEnd_3080753 : Nat := 4983230072969 + 3 ^ 40 * 3080753 * 2
def baseEnd_3080753 : Nat := 351534903729086727426529

theorem tailTrace_3080753 : CollatzResearch.WordTrace tailWord_3080753 prefixEnd_3080753 351534903729086727426529 := by
  unfold tailWord_3080753
  simp only [CollatzResearch.WordTrace]
  refine ⟨112364293007965506568510913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74909528671977004379007275 112364293007965506568510913)
  ·
    refine ⟨84273219755974129926383185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112364293007965506568510913 84273219755974129926383185)
    ·
      refine ⟨63204914816980597444787389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84273219755974129926383185 63204914816980597444787389)
      ·
        refine ⟨23701843056367724041795271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63204914816980597444787389 23701843056367724041795271)
        ·
          refine ⟨35552764584551586062692907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23701843056367724041795271 35552764584551586062692907)
          ·
            refine ⟨53329146876827379094039361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35552764584551586062692907 53329146876827379094039361)
            ·
              refine ⟨39996860157620534320529521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53329146876827379094039361 39996860157620534320529521)
              ·
                refine ⟨29997645118215400740397141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39996860157620534320529521 29997645118215400740397141)
                ·
                  refine ⟨351534903729086727426529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29997645118215400740397141 351534903729086727426529)
                  ·
                    rfl

theorem cell22_3080753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_3080753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080753 prefixEnd_3080753 := by exact prefixLift 3080753
  have htrace : WordTrace (prefixWord ++ tailWord_3080753) baseStart_3080753 baseEnd_3080753 := by
    simpa [prefixWord, tailWord_3080753, baseEnd_3080753] using wordTrace_append hprefix tailTrace_3080753
  have hstable : (prefixWord ++ tailWord_3080753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080753).length < 2 ^ (prefixWord ++ tailWord_3080753).sum := by decide
  have hdescent : baseEnd_3080753 < baseStart_3080753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080755 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 1, 4]
def baseStart_3080755 : Nat := 118140960795 + 3080755 * 2 ^ 59
def prefixEnd_3080755 : Nat := 4983230072969 + 3 ^ 40 * 3080755 * 2
def baseEnd_3080755 : Nat := 1054605395828132843729581

theorem tailTrace_3080755 : CollatzResearch.WordTrace tailWord_3080755 prefixEnd_3080755 1054605395828132843729581 := by
  unfold tailWord_3080755
  simp only [CollatzResearch.WordTrace]
  refine ⟨112364365953958260910083719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74909577302638840606722479 112364365953958260910083719)
  ·
    refine ⟨168546548930937391365125579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112364365953958260910083719 168546548930937391365125579)
    ·
      refine ⟨252819823396406087047688369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168546548930937391365125579 252819823396406087047688369)
      ·
        refine ⟨189614867547304565285766277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252819823396406087047688369 189614867547304565285766277)
        ·
          refine ⟨35552787665119605991081177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189614867547304565285766277 35552787665119605991081177)
          ·
            refine ⟨26664590748839704493310883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35552787665119605991081177 26664590748839704493310883)
            ·
              refine ⟨39996886123259556739966325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26664590748839704493310883 39996886123259556739966325)
              ·
                refine ⟨3749708074055583444371843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39996886123259556739966325 3749708074055583444371843)
                ·
                  refine ⟨5624562111083375166557765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749708074055583444371843 5624562111083375166557765)
                  ·
                    refine ⟨1054605395828132843729581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624562111083375166557765 1054605395828132843729581)
                    ·
                      rfl

theorem cell22_3080755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 4].length) (baseStart_3080755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080755 prefixEnd_3080755 := by exact prefixLift 3080755
  have htrace : WordTrace (prefixWord ++ tailWord_3080755) baseStart_3080755 baseEnd_3080755 := by
    simpa [prefixWord, tailWord_3080755, baseEnd_3080755] using wordTrace_append hprefix tailTrace_3080755
  have hstable : (prefixWord ++ tailWord_3080755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080755).length < 2 ^ (prefixWord ++ tailWord_3080755).sum := by decide
  have hdescent : baseEnd_3080755 < baseStart_3080755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080783 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3080783 : Nat := 118140960795 + 3080783 * 2 ^ 59
def prefixEnd_3080783 : Nat := 4983230072969 + 3 ^ 40 * 3080783 * 2
def baseEnd_3080783 : Nat := 1054614980800350104029495

theorem tailTrace_3080783 : CollatzResearch.WordTrace tailWord_3080783 prefixEnd_3080783 1054614980800350104029495 := by
  unfold tailWord_3080783
  simp only [CollatzResearch.WordTrace]
  refine ⟨112365387197856821692103003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74910258131904547794735335 112365387197856821692103003)
  ·
    refine ⟨168548080796785232538154505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112365387197856821692103003 168548080796785232538154505)
    ·
      refine ⟨126411060597588924403615879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168548080796785232538154505 126411060597588924403615879)
      ·
        refine ⟨189616590896383386605423819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126411060597588924403615879 189616590896383386605423819)
        ·
          refine ⟨284424886344575079908135729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189616590896383386605423819 284424886344575079908135729)
          ·
            refine ⟨213318664758431309931101797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284424886344575079908135729 213318664758431309931101797)
            ·
              refine ⟨39997249642205870612081587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213318664758431309931101797 39997249642205870612081587)
              ·
                refine ⟨59995874463308805918122381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39997249642205870612081587 59995874463308805918122381)
                ·
                  refine ⟨22498452923740802219295893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59995874463308805918122381 22498452923740802219295893)
                  ·
                    refine ⟨1054614980800350104029495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22498452923740802219295893 1054614980800350104029495)
                    ·
                      rfl

theorem cell22_3080783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3080783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080783 prefixEnd_3080783 := by exact prefixLift 3080783
  have htrace : WordTrace (prefixWord ++ tailWord_3080783) baseStart_3080783 baseEnd_3080783 := by
    simpa [prefixWord, tailWord_3080783, baseEnd_3080783] using wordTrace_append hprefix tailTrace_3080783
  have hstable : (prefixWord ++ tailWord_3080783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080783).length < 2 ^ (prefixWord ++ tailWord_3080783).sum := by decide
  have hdescent : baseEnd_3080783 < baseStart_3080783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080800 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_3080800 : Nat := 118140960795 + 3080800 * 2 ^ 59
def prefixEnd_3080800 : Nat := 4983230072969 + 3 ^ 40 * 3080800 * 2
def baseEnd_3080800 : Nat := 1054620800247767726354443

theorem tailTrace_3080800 : CollatzResearch.WordTrace tailWord_3080800 prefixEnd_3080800 1054620800247767726354443 := by
  unfold tailWord_3080800
  simp only [CollatzResearch.WordTrace]
  refine ⟨56183003619397616797735927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74910671492530155730314569 56183003619397616797735927)
  ·
    refine ⟨84274505429096425196603891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56183003619397616797735927 84274505429096425196603891)
    ·
      refine ⟨126411758143644637794905837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84274505429096425196603891 126411758143644637794905837)
      ·
        refine ⟨47404409303866739173089689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126411758143644637794905837 47404409303866739173089689)
        ·
          refine ⟨35553306977900054379817267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47404409303866739173089689 35553306977900054379817267)
          ·
            refine ⟨53329960466850081569725901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35553306977900054379817267 53329960466850081569725901)
            ·
              refine ⟨19998735175068780588647213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53329960466850081569725901 19998735175068780588647213)
              ·
                refine ⟨7499525690650792720742705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19998735175068780588647213 7499525690650792720742705)
                ·
                  refine ⟨5624644267988094540557029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7499525690650792720742705 5624644267988094540557029)
                  ·
                    refine ⟨1054620800247767726354443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5624644267988094540557029 1054620800247767726354443)
                    ·
                      rfl

theorem cell22_3080800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_3080800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080800 prefixEnd_3080800 := by exact prefixLift 3080800
  have htrace : WordTrace (prefixWord ++ tailWord_3080800) baseStart_3080800 baseEnd_3080800 := by
    simpa [prefixWord, tailWord_3080800, baseEnd_3080800] using wordTrace_append hprefix tailTrace_3080800
  have hstable : (prefixWord ++ tailWord_3080800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080800).length < 2 ^ (prefixWord ++ tailWord_3080800).sum := by decide
  have hdescent : baseEnd_3080800 < baseStart_3080800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080877 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3080877 : Nat := 118140960795 + 3080877 * 2 ^ 59
def prefixEnd_3080877 : Nat := 4983230072969 + 3 ^ 40 * 3080877 * 2
def baseEnd_3080877 : Nat := 351549052973788397393069

theorem tailTrace_3080877 : CollatzResearch.WordTrace tailWord_3080877 prefixEnd_3080877 351549052973788397393069 := by
  unfold tailWord_3080877
  simp only [CollatzResearch.WordTrace]
  refine ⟨112368815659516275746024885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74912543773010850497349923 112368815659516275746024885)
  ·
    refine ⟨10534576468079650851189833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112368815659516275746024885 10534576468079650851189833)
    ·
      refine ⟨7900932351059738138392375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10534576468079650851189833 7900932351059738138392375)
      ·
        refine ⟨11851398526589607207588563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7900932351059738138392375 11851398526589607207588563)
        ·
          refine ⟨17777097789884410811382845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11851398526589607207588563 17777097789884410811382845)
          ·
            refine ⟨6666411671206654054268567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17777097789884410811382845 6666411671206654054268567)
            ·
              refine ⟨9999617506809981081402851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666411671206654054268567 9999617506809981081402851)
              ·
                refine ⟨14999426260214971622104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9999617506809981081402851 14999426260214971622104277)
                ·
                  refine ⟨351549052973788397393069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14999426260214971622104277 351549052973788397393069)
                  ·
                    rfl

theorem cell22_3080877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3080877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080877 prefixEnd_3080877 := by exact prefixLift 3080877
  have htrace : WordTrace (prefixWord ++ tailWord_3080877) baseStart_3080877 baseEnd_3080877 := by
    simpa [prefixWord, tailWord_3080877, baseEnd_3080877] using wordTrace_append hprefix tailTrace_3080877
  have hstable : (prefixWord ++ tailWord_3080877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080877).length < 2 ^ (prefixWord ++ tailWord_3080877).sum := by decide
  have hdescent : baseEnd_3080877 < baseStart_3080877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080881 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_3080881 : Nat := 118140960795 + 3080881 * 2 ^ 59
def prefixEnd_3080881 : Nat := 4983230072969 + 3 ^ 40 * 3080881 * 2
def baseEnd_3080881 : Nat := 1054648528203110515079195

theorem tailTrace_3080881 : CollatzResearch.WordTrace tailWord_3080881 prefixEnd_3080881 1054648528203110515079195 := by
  unfold tailWord_3080881
  simp only [CollatzResearch.WordTrace]
  refine ⟨112368961551501784429170497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74912641034334522952780331 112368961551501784429170497)
  ·
    refine ⟨84276721163626338321877873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112368961551501784429170497 84276721163626338321877873)
    ·
      refine ⟨63207540872719753741408405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84276721163626338321877873 63207540872719753741408405)
      ·
        refine ⟨2962853478408738456628519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63207540872719753741408405 2962853478408738456628519)
        ·
          refine ⟨4444280217613107684942779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962853478408738456628519 4444280217613107684942779)
          ·
            refine ⟨6666420326419661527414169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444280217613107684942779 6666420326419661527414169)
            ·
              refine ⟨4999815244814746145560627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666420326419661527414169 4999815244814746145560627)
              ·
                refine ⟨7499722867222119218340941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999815244814746145560627 7499722867222119218340941)
                ·
                  refine ⟨2812396075208294706877853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7499722867222119218340941 2812396075208294706877853)
                  ·
                    refine ⟨1054648528203110515079195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812396075208294706877853 1054648528203110515079195)
                    ·
                      rfl

theorem cell22_3080881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_3080881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080881 prefixEnd_3080881 := by exact prefixLift 3080881
  have htrace : WordTrace (prefixWord ++ tailWord_3080881) baseStart_3080881 baseEnd_3080881 := by
    simpa [prefixWord, tailWord_3080881, baseEnd_3080881] using wordTrace_append hprefix tailTrace_3080881
  have hstable : (prefixWord ++ tailWord_3080881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080881).length < 2 ^ (prefixWord ++ tailWord_3080881).sum := by decide
  have hdescent : baseEnd_3080881 < baseStart_3080881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080894 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_3080894 : Nat := 118140960795 + 3080894 * 2 ^ 59
def prefixEnd_3080894 : Nat := 4983230072969 + 3 ^ 40 * 3080894 * 2
def baseEnd_3080894 : Nat := 351550992789594271501385

theorem tailTrace_3080894 : CollatzResearch.WordTrace tailWord_3080894 prefixEnd_3080894 351550992789594271501385 := by
  unfold tailWord_3080894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14046179462556835956174217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74912957133636458432929157 14046179462556835956174217)
  ·
    refine ⟨10534634596917626967130663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14046179462556835956174217 10534634596917626967130663)
    ·
      refine ⟨15801951895376440450695995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10534634596917626967130663 15801951895376440450695995)
      ·
        refine ⟨23702927843064660676043993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15801951895376440450695995 23702927843064660676043993)
        ·
          refine ⟨17777195882298495507032995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23702927843064660676043993 17777195882298495507032995)
          ·
            refine ⟨26665793823447743260549493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17777195882298495507032995 26665793823447743260549493)
            ·
              refine ⟨2499918170948225930676515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26665793823447743260549493 2499918170948225930676515)
              ·
                refine ⟨3749877256422338896014773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499918170948225930676515 3749877256422338896014773)
                ·
                  refine ⟨351550992789594271501385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3749877256422338896014773 351550992789594271501385)
                  ·
                    rfl

theorem cell22_3080894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_3080894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080894 prefixEnd_3080894 := by exact prefixLift 3080894
  have htrace : WordTrace (prefixWord ++ tailWord_3080894) baseStart_3080894 baseEnd_3080894 := by
    simpa [prefixWord, tailWord_3080894, baseEnd_3080894] using wordTrace_append hprefix tailTrace_3080894
  have hstable : (prefixWord ++ tailWord_3080894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080894).length < 2 ^ (prefixWord ++ tailWord_3080894).sum := by decide
  have hdescent : baseEnd_3080894 < baseStart_3080894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080937 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_3080937 : Nat := 118140960795 + 3080937 * 2 ^ 59
def prefixEnd_3080937 : Nat := 4983230072969 + 3 ^ 40 * 3080937 * 2
def baseEnd_3080937 : Nat := 1054667698147545035679023

theorem tailTrace_3080937 : CollatzResearch.WordTrace tailWord_3080937 prefixEnd_3080937 1054667698147545035679023 := by
  unfold tailWord_3080937
  simp only [CollatzResearch.WordTrace]
  refine ⟨112371004039298905993209065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74914002692865937328806043 112371004039298905993209065)
  ·
    refine ⟨84278253029474179494906799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112371004039298905993209065 84278253029474179494906799)
    ·
      refine ⟨126417379544211269242360199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84278253029474179494906799 126417379544211269242360199)
      ·
        refine ⟨189626069316316903863540299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126417379544211269242360199 189626069316316903863540299)
        ·
          refine ⟨284439103974475355795310449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189626069316316903863540299 284439103974475355795310449)
          ·
            refine ⟨213329327980856516846482837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284439103974475355795310449 213329327980856516846482837)
            ·
              refine ⟨9999812249102649227178883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213329327980856516846482837 9999812249102649227178883)
              ·
                refine ⟨14999718373653973840768325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9999812249102649227178883 14999718373653973840768325)
                ·
                  refine ⟨2812447195060120095144061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14999718373653973840768325 2812447195060120095144061)
                  ·
                    refine ⟨1054667698147545035679023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812447195060120095144061 1054667698147545035679023)
                    ·
                      rfl

theorem cell22_3080937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_3080937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080937 prefixEnd_3080937 := by exact prefixLift 3080937
  have htrace : WordTrace (prefixWord ++ tailWord_3080937) baseStart_3080937 baseEnd_3080937 := by
    simpa [prefixWord, tailWord_3080937, baseEnd_3080937] using wordTrace_append hprefix tailTrace_3080937
  have hstable : (prefixWord ++ tailWord_3080937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080937).length < 2 ^ (prefixWord ++ tailWord_3080937).sum := by decide
  have hdescent : baseEnd_3080937 < baseStart_3080937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080965 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_3080965 : Nat := 118140960795 + 3080965 * 2 ^ 59
def prefixEnd_3080965 : Nat := 4983230072969 + 3 ^ 40 * 3080965 * 2
def baseEnd_3080965 : Nat := 1054677283119762295978937

theorem tailTrace_3080965 : CollatzResearch.WordTrace tailWord_3080965 prefixEnd_3080965 1054677283119762295978937 := by
  unfold tailWord_3080965
  simp only [CollatzResearch.WordTrace]
  refine ⟨112372025283197466775228349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74914683522131644516818899 112372025283197466775228349)
  ·
    refine ⟨42139509481199050040710631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112372025283197466775228349 42139509481199050040710631)
    ·
      refine ⟨63209264221798575061065947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42139509481199050040710631 63209264221798575061065947)
      ·
        refine ⟨94813896332697862591598921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63209264221798575061065947 94813896332697862591598921)
        ·
          refine ⟨71110422249523396943699191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94813896332697862591598921 71110422249523396943699191)
          ·
            refine ⟨106665633374285095415548787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71110422249523396943699191 106665633374285095415548787)
            ·
              refine ⟨159998450061427643123323181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106665633374285095415548787 159998450061427643123323181)
              ·
                refine ⟨59999418773035366171246193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159998450061427643123323181 59999418773035366171246193)
                ·
                  refine ⟨44999564079776524628434645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59999418773035366171246193 44999564079776524628434645)
                  ·
                    refine ⟨1054677283119762295978937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44999564079776524628434645 1054677283119762295978937)
                    ·
                      rfl

theorem cell22_3080965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_3080965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080965 prefixEnd_3080965 := by exact prefixLift 3080965
  have htrace : WordTrace (prefixWord ++ tailWord_3080965) baseStart_3080965 baseEnd_3080965 := by
    simpa [prefixWord, tailWord_3080965, baseEnd_3080965] using wordTrace_append hprefix tailTrace_3080965
  have hstable : (prefixWord ++ tailWord_3080965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080965).length < 2 ^ (prefixWord ++ tailWord_3080965).sum := by decide
  have hdescent : baseEnd_3080965 < baseStart_3080965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080967 : List Nat := [1, 1, 4, 4, 1, 1, 2, 8]
def baseStart_3080967 : Nat := 118140960795 + 3080967 * 2 ^ 59
def prefixEnd_3080967 : Nat := 4983230072969 + 3 ^ 40 * 3080967 * 2
def baseEnd_3080967 : Nat := 117186440862292773047659

theorem tailTrace_3080967 : CollatzResearch.WordTrace tailWord_3080967 prefixEnd_3080967 117186440862292773047659 := by
  unfold tailWord_3080967
  simp only [CollatzResearch.WordTrace]
  refine ⟨112372098229190221116801155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74914732152793480744534103 112372098229190221116801155)
  ·
    refine ⟨168558147343785331675201733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112372098229190221116801155 168558147343785331675201733)
    ·
      refine ⟨31604652626959749689100325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168558147343785331675201733 31604652626959749689100325)
      ·
        refine ⟨5925872367554953066706311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31604652626959749689100325 5925872367554953066706311)
        ·
          refine ⟨8888808551332429600059467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5925872367554953066706311 8888808551332429600059467)
          ·
            refine ⟨13333212826998644400089201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888808551332429600059467 13333212826998644400089201)
            ·
              refine ⟨9999909620248983300066901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13333212826998644400089201 9999909620248983300066901)
              ·
                refine ⟨117186440862292773047659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9999909620248983300066901 117186440862292773047659)
                ·
                  rfl

theorem cell22_3080967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 8].length) (baseStart_3080967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3080967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3080967 prefixEnd_3080967 := by exact prefixLift 3080967
  have htrace : WordTrace (prefixWord ++ tailWord_3080967) baseStart_3080967 baseEnd_3080967 := by
    simpa [prefixWord, tailWord_3080967, baseEnd_3080967] using wordTrace_append hprefix tailTrace_3080967
  have hstable : (prefixWord ++ tailWord_3080967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080967).length < 2 ^ (prefixWord ++ tailWord_3080967).sum := by decide
  have hdescent : baseEnd_3080967 < baseStart_3080967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081087 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_3081087 : Nat := 118140960795 + 3081087 * 2 ^ 59
def prefixEnd_3081087 : Nat := 4983230072969 + 3 ^ 40 * 3081087 * 2
def baseEnd_3081087 : Nat := 1054719046212994644428563

theorem tailTrace_3081087 : CollatzResearch.WordTrace tailWord_3081087 prefixEnd_3081087 1054719046212994644428563 := by
  unfold tailWord_3081087
  simp only [CollatzResearch.WordTrace]
  refine ⟨112376474988755481611169515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74917649992503654407446343 112376474988755481611169515)
  ·
    refine ⟨168564712483133222416754273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112376474988755481611169515 168564712483133222416754273)
    ·
      refine ⟨126423534362349916812565705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168564712483133222416754273 126423534362349916812565705)
      ·
        refine ⟨94817650771762437609424279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126423534362349916812565705 94817650771762437609424279)
        ·
          refine ⟨142226476157643656414136419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94817650771762437609424279 142226476157643656414136419)
          ·
            refine ⟨213339714236465484621204629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142226476157643656414136419 213339714236465484621204629)
            ·
              refine ⟨10000299104834319591618967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213339714236465484621204629 10000299104834319591618967)
              ·
                refine ⟨15000448657251479387428451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10000299104834319591618967 15000448657251479387428451)
                ·
                  refine ⟨22500672985877219081142677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15000448657251479387428451 22500672985877219081142677)
                  ·
                    refine ⟨1054719046212994644428563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22500672985877219081142677 1054719046212994644428563)
                    ·
                      rfl

theorem cell22_3081087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_3081087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081087 prefixEnd_3081087 := by exact prefixLift 3081087
  have htrace : WordTrace (prefixWord ++ tailWord_3081087) baseStart_3081087 baseEnd_3081087 := by
    simpa [prefixWord, tailWord_3081087, baseEnd_3081087] using wordTrace_append hprefix tailTrace_3081087
  have hstable : (prefixWord ++ tailWord_3081087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081087).length < 2 ^ (prefixWord ++ tailWord_3081087).sum := by decide
  have hdescent : baseEnd_3081087 < baseStart_3081087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081108 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3081108 : Nat := 118140960795 + 3081108 * 2 ^ 59
def prefixEnd_3081108 : Nat := 4983230072969 + 3 ^ 40 * 3081108 * 2
def baseEnd_3081108 : Nat := 351575411647385863217833

theorem tailTrace_3081108 : CollatzResearch.WordTrace tailWord_3081108 prefixEnd_3081108 351575411647385863217833 := by
  unfold tailWord_3081108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56188620460839701098841989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74918160614452934798455985 56188620460839701098841989)
  ·
    refine ⟨10535366336407443956032873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56188620460839701098841989 10535366336407443956032873)
    ·
      refine ⟨7901524752305582967024655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10535366336407443956032873 7901524752305582967024655)
      ·
        refine ⟨11852287128458374450536983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7901524752305582967024655 11852287128458374450536983)
        ·
          refine ⟨17778430692687561675805475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11852287128458374450536983 17778430692687561675805475)
          ·
            refine ⟨26667646039031342513708213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17778430692687561675805475 26667646039031342513708213)
            ·
              refine ⟨2500091816159188360660145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26667646039031342513708213 2500091816159188360660145)
              ·
                refine ⟨1875068862119391270495109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500091816159188360660145 1875068862119391270495109)
                ·
                  refine ⟨351575411647385863217833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875068862119391270495109 351575411647385863217833)
                  ·
                    rfl

theorem cell22_3081108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3081108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081108 prefixEnd_3081108 := by exact prefixLift 3081108
  have htrace : WordTrace (prefixWord ++ tailWord_3081108) baseStart_3081108 baseEnd_3081108 := by
    simpa [prefixWord, tailWord_3081108, baseEnd_3081108] using wordTrace_append hprefix tailTrace_3081108
  have hstable : (prefixWord ++ tailWord_3081108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081108).length < 2 ^ (prefixWord ++ tailWord_3081108).sum := by decide
  have hdescent : baseEnd_3081108 < baseStart_3081108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081119 : List Nat := [1, 1, 2, 5, 2, 2, 2, 7]
def baseStart_3081119 : Nat := 118140960795 + 3081119 * 2 ^ 59
def prefixEnd_3081119 : Nat := 4983230072969 + 3 ^ 40 * 3081119 * 2
def baseEnd_3081119 : Nat := 117192222274106358625385

theorem tailTrace_3081119 : CollatzResearch.WordTrace tailWord_3081119 prefixEnd_3081119 117192222274106358625385 := by
  unfold tailWord_3081119
  simp only [CollatzResearch.WordTrace]
  refine ⟨112377642124639551076334411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74918428083093034050889607 112377642124639551076334411)
  ·
    refine ⟨168566463186959326614501617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112377642124639551076334411 168566463186959326614501617)
    ·
      refine ⟨126424847390219494960876213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168566463186959326614501617 126424847390219494960876213)
      ·
        refine ⟨11852329442833077652582145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126424847390219494960876213 11852329442833077652582145)
        ·
          refine ⟨8889247082124808239436609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11852329442833077652582145 8889247082124808239436609)
          ·
            refine ⟨6666935311593606179577457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8889247082124808239436609 6666935311593606179577457)
            ·
              refine ⟨5000201483695204634683093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666935311593606179577457 5000201483695204634683093)
              ·
                refine ⟨117192222274106358625385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5000201483695204634683093 117192222274106358625385)
                ·
                  rfl

theorem cell22_3081119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 7].length) (baseStart_3081119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081119 prefixEnd_3081119 := by exact prefixLift 3081119
  have htrace : WordTrace (prefixWord ++ tailWord_3081119) baseStart_3081119 baseEnd_3081119 := by
    simpa [prefixWord, tailWord_3081119, baseEnd_3081119] using wordTrace_append hprefix tailTrace_3081119
  have hstable : (prefixWord ++ tailWord_3081119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081119).length < 2 ^ (prefixWord ++ tailWord_3081119).sum := by decide
  have hdescent : baseEnd_3081119 < baseStart_3081119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081132 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_3081132 : Nat := 118140960795 + 3081132 * 2 ^ 59
def prefixEnd_3081132 : Nat := 4983230072969 + 3 ^ 40 * 3081132 * 2
def baseEnd_3081132 : Nat := 1054734450632629527053425

theorem tailTrace_3081132 : CollatzResearch.WordTrace tailWord_3081132 prefixEnd_3081132 1054734450632629527053425 := by
  unfold tailWord_3081132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56189058136796227148278825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74918744182394969531038433 56189058136796227148278825)
  ·
    refine ⟨42141793602597170361209119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56189058136796227148278825 42141793602597170361209119)
    ·
      refine ⟨63212690403895755541813679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42141793602597170361209119 63212690403895755541813679)
      ·
        refine ⟨94819035605843633312720519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63212690403895755541813679 94819035605843633312720519)
        ·
          refine ⟨142228553408765449969080779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94819035605843633312720519 142228553408765449969080779)
          ·
            refine ⟨213342830113148174953621169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142228553408765449969080779 213342830113148174953621169)
            ·
              refine ⟨160007122584861131215215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213342830113148174953621169 160007122584861131215215877)
              ·
                refine ⟨30001335484661462102852977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160007122584861131215215877 30001335484661462102852977)
                ·
                  refine ⟨22501001613496096577139733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30001335484661462102852977 22501001613496096577139733)
                  ·
                    refine ⟨1054734450632629527053425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22501001613496096577139733 1054734450632629527053425)
                    ·
                      rfl

theorem cell22_3081132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_3081132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081132 prefixEnd_3081132 := by exact prefixLift 3081132
  have htrace : WordTrace (prefixWord ++ tailWord_3081132) baseStart_3081132 baseEnd_3081132 := by
    simpa [prefixWord, tailWord_3081132, baseEnd_3081132] using wordTrace_append hprefix tailTrace_3081132
  have hstable : (prefixWord ++ tailWord_3081132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081132).length < 2 ^ (prefixWord ++ tailWord_3081132).sum := by decide
  have hdescent : baseEnd_3081132 < baseStart_3081132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081181 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 5]
def baseStart_3081181 : Nat := 118140960795 + 3081181 * 2 ^ 59
def prefixEnd_3081181 : Nat := 4983230072969 + 3 ^ 40 * 3081181 * 2
def baseEnd_3081181 : Nat := 351583741444669910859425

theorem tailTrace_3081181 : CollatzResearch.WordTrace tailWord_3081181 prefixEnd_3081181 351583741444669910859425 := by
  unfold tailWord_3081181
  simp only [CollatzResearch.WordTrace]
  refine ⟨112379903450414935665091397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74919935633609957110060931 112379903450414935665091397)
  ·
    refine ⟨21071231896952800437204637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112379903450414935665091397 21071231896952800437204637)
    ·
      refine ⟨7901711961357300163951739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21071231896952800437204637 7901711961357300163951739)
      ·
        refine ⟨11852567942035950245927609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7901711961357300163951739 11852567942035950245927609)
        ·
          refine ⟨8889425956526962684445707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11852567942035950245927609 8889425956526962684445707)
          ·
            refine ⟨13334138934790444026668561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8889425956526962684445707 13334138934790444026668561)
            ·
              refine ⟨10000604201092833020001421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13334138934790444026668561 10000604201092833020001421)
              ·
                refine ⟨3750226575409812382500533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10000604201092833020001421 3750226575409812382500533)
                ·
                  refine ⟨351583741444669910859425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750226575409812382500533 351583741444669910859425)
                  ·
                    rfl

theorem cell22_3081181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_3081181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081181 prefixEnd_3081181 := by exact prefixLift 3081181
  have htrace : WordTrace (prefixWord ++ tailWord_3081181) baseStart_3081181 baseEnd_3081181 := by
    simpa [prefixWord, tailWord_3081181, baseEnd_3081181] using wordTrace_append hprefix tailTrace_3081181
  have hstable : (prefixWord ++ tailWord_3081181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081181).length < 2 ^ (prefixWord ++ tailWord_3081181).sum := by decide
  have hdescent : baseEnd_3081181 < baseStart_3081181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081202 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3081202 : Nat := 118140960795 + 3081202 * 2 ^ 59
def prefixEnd_3081202 : Nat := 4983230072969 + 3 ^ 40 * 3081202 * 2
def baseEnd_3081202 : Nat := 1054758413063172677803211

theorem tailTrace_3081202 : CollatzResearch.WordTrace tailWord_3081202 prefixEnd_3081202 1054758413063172677803211 := by
  unfold tailWord_3081202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095167345834714062901465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74920446255559237501070573 28095167345834714062901465)
  ·
    refine ⟨21071375509376035547176099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28095167345834714062901465 21071375509376035547176099)
    ·
      refine ⟨31607063264064053320764149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21071375509376035547176099 31607063264064053320764149)
      ·
        refine ⟨2963162181006004998821639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31607063264064053320764149 2963162181006004998821639)
        ·
          refine ⟨4444743271509007498232459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963162181006004998821639 4444743271509007498232459)
          ·
            refine ⟨6667114907263511247348689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444743271509007498232459 6667114907263511247348689)
            ·
              refine ⟨5000336180447633435511517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667114907263511247348689 5000336180447633435511517)
              ·
                refine ⟨1875126067667862538316819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000336180447633435511517 1875126067667862538316819)
                ·
                  refine ⟨2812689101501793807475229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875126067667862538316819 2812689101501793807475229)
                  ·
                    refine ⟨1054758413063172677803211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812689101501793807475229 1054758413063172677803211)
                    ·
                      rfl

theorem cell22_3081202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3081202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081202 prefixEnd_3081202 := by exact prefixLift 3081202
  have htrace : WordTrace (prefixWord ++ tailWord_3081202) baseStart_3081202 baseEnd_3081202 := by
    simpa [prefixWord, tailWord_3081202, baseEnd_3081202] using wordTrace_append hprefix tailTrace_3081202
  have hstable : (prefixWord ++ tailWord_3081202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081202).length < 2 ^ (prefixWord ++ tailWord_3081202).sum := by decide
  have hdescent : baseEnd_3081202 < baseStart_3081202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081226 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_3081226 : Nat := 118140960795 + 3081226 * 2 ^ 59
def prefixEnd_3081226 : Nat := 4983230072969 + 3 ^ 40 * 3081226 * 2
def baseEnd_3081226 : Nat := 351588876251214871734379

theorem tailTrace_3081226 : CollatzResearch.WordTrace tailWord_3081226 prefixEnd_3081226 351588876251214871734379 := by
  unfold tailWord_3081226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095386183812977087619883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74921029823501272233653021 28095386183812977087619883)
  ·
    refine ⟨42143079275719465631429825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095386183812977087619883 42143079275719465631429825)
    ·
      refine ⟨31607309456789599223572369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42143079275719465631429825 31607309456789599223572369)
      ·
        refine ⟨23705482092592199417679277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31607309456789599223572369 23705482092592199417679277)
        ·
          refine ⟨8889555784722074781629729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23705482092592199417679277 8889555784722074781629729)
          ·
            refine ⟨6667166838541556086222297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8889555784722074781629729 6667166838541556086222297)
            ·
              refine ⟨5000375128906167064666723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667166838541556086222297 5000375128906167064666723)
              ·
                refine ⟨7500562693359250597000085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000375128906167064666723 7500562693359250597000085)
                ·
                  refine ⟨351588876251214871734379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7500562693359250597000085 351588876251214871734379)
                  ·
                    rfl

theorem cell22_3081226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_3081226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081226 prefixEnd_3081226 := by exact prefixLift 3081226
  have htrace : WordTrace (prefixWord ++ tailWord_3081226) baseStart_3081226 baseEnd_3081226 := by
    simpa [prefixWord, tailWord_3081226, baseEnd_3081226] using wordTrace_append hprefix tailTrace_3081226
  have hstable : (prefixWord ++ tailWord_3081226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081226).length < 2 ^ (prefixWord ++ tailWord_3081226).sum := by decide
  have hdescent : baseEnd_3081226 < baseStart_3081226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081241 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_3081241 : Nat := 118140960795 + 3081241 * 2 ^ 59
def prefixEnd_3081241 : Nat := 4983230072969 + 3 ^ 40 * 3081241 * 2
def baseEnd_3081241 : Nat := 1054771763560189576078091

theorem tailTrace_3081241 : CollatzResearch.WordTrace tailWord_3081241 prefixEnd_3081241 1054771763560189576078091 := by
  unfold tailWord_3081241
  simp only [CollatzResearch.WordTrace]
  refine ⟨112382091830197565912275577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74921394553465043941517051 112382091830197565912275577)
  ·
    refine ⟨84286568872648174434206683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112382091830197565912275577 84286568872648174434206683)
    ·
      refine ⟨126429853308972261651310025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84286568872648174434206683 126429853308972261651310025)
      ·
        refine ⟨94822389981729196238482519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126429853308972261651310025 94822389981729196238482519)
        ·
          refine ⟨142233584972593794357723779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94822389981729196238482519 142233584972593794357723779)
          ·
            refine ⟨213350377458890691536585669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142233584972593794357723779 213350377458890691536585669)
            ·
              refine ⟨40003195773542004663109813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213350377458890691536585669 40003195773542004663109813)
              ·
                refine ⟨3750299603769562937166545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40003195773542004663109813 3750299603769562937166545)
                ·
                  refine ⟨2812724702827172202874909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750299603769562937166545 2812724702827172202874909)
                  ·
                    refine ⟨1054771763560189576078091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812724702827172202874909 1054771763560189576078091)
                    ·
                      rfl

theorem cell22_3081241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_3081241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081241 prefixEnd_3081241 := by exact prefixLift 3081241
  have htrace : WordTrace (prefixWord ++ tailWord_3081241) baseStart_3081241 baseEnd_3081241 := by
    simpa [prefixWord, tailWord_3081241, baseEnd_3081241] using wordTrace_append hprefix tailTrace_3081241
  have hstable : (prefixWord ++ tailWord_3081241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081241).length < 2 ^ (prefixWord ++ tailWord_3081241).sum := by decide
  have hdescent : baseEnd_3081241 < baseStart_3081241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081376 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_3081376 : Nat := 118140960795 + 3081376 * 2 ^ 59
def prefixEnd_3081376 : Nat := 4983230072969 + 3 ^ 40 * 3081376 * 2
def baseEnd_3081376 : Nat := 1054817976819094223952677

theorem tailTrace_3081376 : CollatzResearch.WordTrace tailWord_3081376 prefixEnd_3081376 1054817976819094223952677 := by
  unfold tailWord_3081376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56193507842354241984219991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74924677123138989312293321 56193507842354241984219991)
  ·
    refine ⟨84290261763531362976329987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56193507842354241984219991 84290261763531362976329987)
    ·
      refine ⟨126435392645297044464494981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84290261763531362976329987 126435392645297044464494981)
      ·
        refine ⟨23706636120993195837092809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126435392645297044464494981 23706636120993195837092809)
        ·
          refine ⟨17779977090744896877819607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23706636120993195837092809 17779977090744896877819607)
          ·
            refine ⟨26669965636117345316729411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17779977090744896877819607 26669965636117345316729411)
            ·
              refine ⟨40004948454176017975094117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26669965636117345316729411 40004948454176017975094117)
              ·
                refine ⟨7500927835158003370330147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40004948454176017975094117 7500927835158003370330147)
                ·
                  refine ⟨11251391752737005055495221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500927835158003370330147 11251391752737005055495221)
                  ·
                    refine ⟨1054817976819094223952677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11251391752737005055495221 1054817976819094223952677)
                    ·
                      rfl

theorem cell22_3081376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_3081376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081376 prefixEnd_3081376 := by exact prefixLift 3081376
  have htrace : WordTrace (prefixWord ++ tailWord_3081376) baseStart_3081376 baseEnd_3081376 := by
    simpa [prefixWord, tailWord_3081376, baseEnd_3081376] using wordTrace_append hprefix tailTrace_3081376
  have hstable : (prefixWord ++ tailWord_3081376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081376).length < 2 ^ (prefixWord ++ tailWord_3081376).sum := by decide
  have hdescent : baseEnd_3081376 < baseStart_3081376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081380 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_3081380 : Nat := 118140960795 + 3081380 * 2 ^ 59
def prefixEnd_3081380 : Nat := 4983230072969 + 3 ^ 40 * 3081380 * 2
def baseEnd_3081380 : Nat := 1054819346100839546852665

theorem tailTrace_3081380 : CollatzResearch.WordTrace tailWord_3081380 prefixEnd_3081380 1054819346100839546852665 := by
  unfold tailWord_3081380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56193580788346996325792797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74924774384462661767723729 56193580788346996325792797)
  ·
    refine ⟨21072592795630123622172299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56193580788346996325792797 21072592795630123622172299)
    ·
      refine ⟨31608889193445185433258449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21072592795630123622172299 31608889193445185433258449)
      ·
        refine ⟨23706666895083889074943837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31608889193445185433258449 23706666895083889074943837)
        ·
          refine ⟨8890000085656458403103939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23706666895083889074943837 8890000085656458403103939)
          ·
            refine ⟨13335000128484687604655909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890000085656458403103939 13335000128484687604655909)
            ·
              refine ⟨2500312524090878925872983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13335000128484687604655909 2500312524090878925872983)
              ·
                refine ⟨3750468786136318388809475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500312524090878925872983 3750468786136318388809475)
                ·
                  refine ⟨5625703179204477583214213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750468786136318388809475 5625703179204477583214213)
                  ·
                    refine ⟨1054819346100839546852665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625703179204477583214213 1054819346100839546852665)
                    ·
                      rfl

theorem cell22_3081380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_3081380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081380 prefixEnd_3081380 := by exact prefixLift 3081380
  have htrace : WordTrace (prefixWord ++ tailWord_3081380) baseStart_3081380 baseEnd_3081380 := by
    simpa [prefixWord, tailWord_3081380, baseEnd_3081380] using wordTrace_append hprefix tailTrace_3081380
  have hstable : (prefixWord ++ tailWord_3081380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081380).length < 2 ^ (prefixWord ++ tailWord_3081380).sum := by decide
  have hdescent : baseEnd_3081380 < baseStart_3081380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081391 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_3081391 : Nat := 118140960795 + 3081391 * 2 ^ 59
def prefixEnd_3081391 : Nat := 4983230072969 + 3 ^ 40 * 3081391 * 2
def baseEnd_3081391 : Nat := 1054823111625639184827631

theorem tailTrace_3081391 : CollatzResearch.WordTrace tailWord_3081391 prefixEnd_3081391 1054823111625639184827631 := by
  unfold tailWord_3081391
  simp only [CollatzResearch.WordTrace]
  refine ⟨112387562779654141530236027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74925041853102761020157351 112387562779654141530236027)
  ·
    refine ⟨168581344169481212295354041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112387562779654141530236027 168581344169481212295354041)
    ·
      refine ⟨126436008127110909221515531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168581344169481212295354041 126436008127110909221515531)
      ·
        refine ⟨189654012190666363832273297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126436008127110909221515531 189654012190666363832273297)
        ·
          refine ⟨142240509142999772874204973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189654012190666363832273297 142240509142999772874204973)
          ·
            refine ⟨53340190928624914827826865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142240509142999772874204973 53340190928624914827826865)
            ·
              refine ⟨40005143196468686120870149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53340190928624914827826865 40005143196468686120870149)
              ·
                refine ⟨7500964349337878647663153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40005143196468686120870149 7500964349337878647663153)
                ·
                  refine ⟨5625723262003408985747365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7500964349337878647663153 5625723262003408985747365)
                  ·
                    refine ⟨1054823111625639184827631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625723262003408985747365 1054823111625639184827631)
                    ·
                      rfl

theorem cell22_3081391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_3081391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081391 prefixEnd_3081391 := by exact prefixLift 3081391
  have htrace : WordTrace (prefixWord ++ tailWord_3081391) baseStart_3081391 baseEnd_3081391 := by
    simpa [prefixWord, tailWord_3081391, baseEnd_3081391] using wordTrace_append hprefix tailTrace_3081391
  have hstable : (prefixWord ++ tailWord_3081391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081391).length < 2 ^ (prefixWord ++ tailWord_3081391).sum := by decide
  have hdescent : baseEnd_3081391 < baseStart_3081391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081451 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 7]
def baseStart_3081451 : Nat := 118140960795 + 3081451 * 2 ^ 59
def prefixEnd_3081451 : Nat := 4983230072969 + 3 ^ 40 * 3081451 * 2
def baseEnd_3081451 : Nat := 351614550283939676109149

theorem tailTrace_3081451 : CollatzResearch.WordTrace tailWord_3081451 prefixEnd_3081451 351614550283939676109149 := by
  unfold tailWord_3081451
  simp only [CollatzResearch.WordTrace]
  refine ⟨112389751159436771777420207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74926500772957847851613471 112389751159436771777420207)
  ·
    refine ⟨168584626739155157666130311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112389751159436771777420207 168584626739155157666130311)
    ·
      refine ⟨252876940108732736499195467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168584626739155157666130311 252876940108732736499195467)
      ·
        refine ⟨379315410163099104748793201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252876940108732736499195467 379315410163099104748793201)
        ·
          refine ⟨284486557622324328561594901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379315410163099104748793201 284486557622324328561594901)
          ·
            refine ⟨13335307388546452901324761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 284486557622324328561594901 13335307388546452901324761)
            ·
              refine ⟨10001480541409839675993571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13335307388546452901324761 10001480541409839675993571)
              ·
                refine ⟨15002220812114759513990357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001480541409839675993571 15002220812114759513990357)
                ·
                  refine ⟨351614550283939676109149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15002220812114759513990357 351614550283939676109149)
                  ·
                    rfl

theorem cell22_3081451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_3081451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081451 prefixEnd_3081451 := by exact prefixLift 3081451
  have htrace : WordTrace (prefixWord ++ tailWord_3081451) baseStart_3081451 baseEnd_3081451 := by
    simpa [prefixWord, tailWord_3081451, baseEnd_3081451] using wordTrace_append hprefix tailTrace_3081451
  have hstable : (prefixWord ++ tailWord_3081451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081451).length < 2 ^ (prefixWord ++ tailWord_3081451).sum := by decide
  have hdescent : baseEnd_3081451 < baseStart_3081451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081466 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_3081466 : Nat := 118140960795 + 3081466 * 2 ^ 59
def prefixEnd_3081466 : Nat := 4983230072969 + 3 ^ 40 * 3081466 * 2
def baseEnd_3081466 : Nat := 1054848785658363989202401

theorem tailTrace_3081466 : CollatzResearch.WordTrace tailWord_3081466 prefixEnd_3081466 1054848785658363989202401 := by
  unfold tailWord_3081466
  simp only [CollatzResearch.WordTrace]
  refine ⟨28097574563595607334804063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74926865502921619559477501 28097574563595607334804063)
  ·
    refine ⟨42146361845393411002206095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28097574563595607334804063 42146361845393411002206095)
    ·
      refine ⟨63219542768090116503309143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42146361845393411002206095 63219542768090116503309143)
      ·
        refine ⟨94829314152135174754963715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63219542768090116503309143 94829314152135174754963715)
        ·
          refine ⟨142243971228202762132445573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94829314152135174754963715 142243971228202762132445573)
          ·
            refine ⟨26670744605288017899833545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142243971228202762132445573 26670744605288017899833545)
            ·
              refine ⟨20003058453966013424875159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26670744605288017899833545 20003058453966013424875159)
              ·
                refine ⟨30004587680949020137312739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20003058453966013424875159 30004587680949020137312739)
                ·
                  refine ⟨45006881521423530205969109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30004587680949020137312739 45006881521423530205969109)
                  ·
                    refine ⟨1054848785658363989202401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45006881521423530205969109 1054848785658363989202401)
                    ·
                      rfl

theorem cell22_3081466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_3081466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081466 prefixEnd_3081466 := by exact prefixLift 3081466
  have htrace : WordTrace (prefixWord ++ tailWord_3081466) baseStart_3081466 baseEnd_3081466 := by
    simpa [prefixWord, tailWord_3081466, baseEnd_3081466] using wordTrace_append hprefix tailTrace_3081466
  have hstable : (prefixWord ++ tailWord_3081466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081466).length < 2 ^ (prefixWord ++ tailWord_3081466).sum := by decide
  have hdescent : baseEnd_3081466 < baseStart_3081466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081506 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3081506 : Nat := 118140960795 + 3081506 * 2 ^ 59
def prefixEnd_3081506 : Nat := 4983230072969 + 3 ^ 40 * 3081506 * 2
def baseEnd_3081506 : Nat := 1054862478475817218202279

theorem tailTrace_3081506 : CollatzResearch.WordTrace tailWord_3081506 prefixEnd_3081506 1054862478475817218202279 := by
  unfold tailWord_3081506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28097939293559379042668093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74927838116158344113781581 28097939293559379042668093)
  ·
    refine ⟨10536727235084767141000535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28097939293559379042668093 10536727235084767141000535)
    ·
      refine ⟨15805090852627150711500803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10536727235084767141000535 15805090852627150711500803)
      ·
        refine ⟨23707636278940726067251205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805090852627150711500803 23707636278940726067251205)
        ·
          refine ⟨4445181802301386137609601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23707636278940726067251205 4445181802301386137609601)
          ·
            refine ⟨3333886351726039603207201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4445181802301386137609601 3333886351726039603207201)
            ·
              refine ⟨2500414763794529702405401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3333886351726039603207201 2500414763794529702405401)
              ·
                refine ⟨1875311072845897276804051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500414763794529702405401 1875311072845897276804051)
                ·
                  refine ⟨2812966609268845915206077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875311072845897276804051 2812966609268845915206077)
                  ·
                    refine ⟨1054862478475817218202279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812966609268845915206077 1054862478475817218202279)
                    ·
                      rfl

theorem cell22_3081506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3081506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081506 prefixEnd_3081506 := by exact prefixLift 3081506
  have htrace : WordTrace (prefixWord ++ tailWord_3081506) baseStart_3081506 baseEnd_3081506 := by
    simpa [prefixWord, tailWord_3081506, baseEnd_3081506] using wordTrace_append hprefix tailTrace_3081506
  have hstable : (prefixWord ++ tailWord_3081506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081506).length < 2 ^ (prefixWord ++ tailWord_3081506).sum := by decide
  have hdescent : baseEnd_3081506 < baseStart_3081506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081528 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_3081528 : Nat := 118140960795 + 3081528 * 2 ^ 59
def prefixEnd_3081528 : Nat := 4983230072969 + 3 ^ 40 * 3081528 * 2
def baseEnd_3081528 : Nat := 1054870009525416494152211

theorem tailTrace_3081528 : CollatzResearch.WordTrace tailWord_3081528 prefixEnd_3081528 1054870009525416494152211 := by
  unfold tailWord_3081528
  simp only [CollatzResearch.WordTrace]
  refine ⟨56196279790078906963986619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74928373053438542618648825 56196279790078906963986619)
  ·
    refine ⟨84294419685118360445979929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56196279790078906963986619 84294419685118360445979929)
    ·
      refine ⟨63220814763838770334484947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84294419685118360445979929 63220814763838770334484947)
      ·
        refine ⟨94831222145758155501727421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63220814763838770334484947 94831222145758155501727421)
        ·
          refine ⟨35561708304659308313147783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94831222145758155501727421 35561708304659308313147783)
          ·
            refine ⟨53342562456988962469721675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35561708304659308313147783 53342562456988962469721675)
            ·
              refine ⟨80013843685483443704582513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53342562456988962469721675 80013843685483443704582513)
              ·
                refine ⟨60010382764112582778436885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80013843685483443704582513 60010382764112582778436885)
                ·
                  refine ⟨2812986692067777317739229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60010382764112582778436885 2812986692067777317739229)
                  ·
                    refine ⟨1054870009525416494152211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812986692067777317739229 1054870009525416494152211)
                    ·
                      rfl

theorem cell22_3081528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_3081528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081528 prefixEnd_3081528 := by exact prefixLift 3081528
  have htrace : WordTrace (prefixWord ++ tailWord_3081528) baseStart_3081528 baseEnd_3081528 := by
    simpa [prefixWord, tailWord_3081528, baseEnd_3081528] using wordTrace_append hprefix tailTrace_3081528
  have hstable : (prefixWord ++ tailWord_3081528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081528).length < 2 ^ (prefixWord ++ tailWord_3081528).sum := by decide
  have hdescent : baseEnd_3081528 < baseStart_3081528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081541 : List Nat := [1, 3, 1, 1, 1, 2, 1, 12]
def baseStart_3081541 : Nat := 118140960795 + 3081541 * 2 ^ 59
def prefixEnd_3081541 : Nat := 4983230072969 + 3 ^ 40 * 3081541 * 2
def baseEnd_3081541 : Nat := 117208273299009865953019

theorem tailTrace_3081541 : CollatzResearch.WordTrace tailWord_3081541 prefixEnd_3081541 117208273299009865953019 := by
  unfold tailWord_3081541
  simp only [CollatzResearch.WordTrace]
  refine ⟨112393033729110717148196477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74928689152740478098797651 112393033729110717148196477)
  ·
    refine ⟨42147387648416518930573679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112393033729110717148196477 42147387648416518930573679)
    ·
      refine ⟨63221081472624778395860519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42147387648416518930573679 63221081472624778395860519)
      ·
        refine ⟨94831622208937167593790779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63221081472624778395860519 94831622208937167593790779)
        ·
          refine ⟨142247433313405751390686169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94831622208937167593790779 142247433313405751390686169)
          ·
            refine ⟨106685574985054313543014627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142247433313405751390686169 106685574985054313543014627)
            ·
              refine ⟨160028362477581470314521941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106685574985054313543014627 160028362477581470314521941)
              ·
                refine ⟨117208273299009865953019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 160028362477581470314521941 117208273299009865953019)
                ·
                  rfl

theorem cell22_3081541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 12].length) (baseStart_3081541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081541 prefixEnd_3081541 := by exact prefixLift 3081541
  have htrace : WordTrace (prefixWord ++ tailWord_3081541) baseStart_3081541 baseEnd_3081541 := by
    simpa [prefixWord, tailWord_3081541, baseEnd_3081541] using wordTrace_append hprefix tailTrace_3081541
  have hstable : (prefixWord ++ tailWord_3081541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081541).length < 2 ^ (prefixWord ++ tailWord_3081541).sum := by decide
  have hdescent : baseEnd_3081541 < baseStart_3081541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081543 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3081543 : Nat := 118140960795 + 3081543 * 2 ^ 59
def prefixEnd_3081543 : Nat := 4983230072969 + 3 ^ 40 * 3081543 * 2
def baseEnd_3081543 : Nat := 1054875144331961455027165

theorem tailTrace_3081543 : CollatzResearch.WordTrace tailWord_3081543 prefixEnd_3081543 1054875144331961455027165 := by
  unfold tailWord_3081543
  simp only [CollatzResearch.WordTrace]
  refine ⟨112393106675103471489769283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74928737783402314326512855 112393106675103471489769283)
  ·
    refine ⟨168589660012655207234653925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112393106675103471489769283 168589660012655207234653925)
    ·
      refine ⟨31610561252372851356497611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168589660012655207234653925 31610561252372851356497611)
      ·
        refine ⟨47415841878559277034746417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31610561252372851356497611 47415841878559277034746417)
        ·
          refine ⟨35561881408919457776059813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47415841878559277034746417 35561881408919457776059813)
          ·
            refine ⟨6667852764172398333011215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35561881408919457776059813 6667852764172398333011215)
            ·
              refine ⟨10001779146258597499516823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667852764172398333011215 10001779146258597499516823)
              ·
                refine ⟨15002668719387896249275235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001779146258597499516823 15002668719387896249275235)
                ·
                  refine ⟨22504003079081844373912853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002668719387896249275235 22504003079081844373912853)
                  ·
                    refine ⟨1054875144331961455027165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22504003079081844373912853 1054875144331961455027165)
                    ·
                      rfl

theorem cell22_3081543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3081543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081543 prefixEnd_3081543 := by exact prefixLift 3081543
  have htrace : WordTrace (prefixWord ++ tailWord_3081543) baseStart_3081543 baseEnd_3081543 := by
    simpa [prefixWord, tailWord_3081543, baseEnd_3081543] using wordTrace_append hprefix tailTrace_3081543
  have hstable : (prefixWord ++ tailWord_3081543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081543).length < 2 ^ (prefixWord ++ tailWord_3081543).sum := by decide
  have hdescent : baseEnd_3081543 < baseStart_3081543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081549 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3081549 : Nat := 118140960795 + 3081549 * 2 ^ 59
def prefixEnd_3081549 : Nat := 4983230072969 + 3 ^ 40 * 3081549 * 2
def baseEnd_3081549 : Nat := 1054877198254579439377147

theorem tailTrace_3081549 : CollatzResearch.WordTrace tailWord_3081549 prefixEnd_3081549 1054877198254579439377147 := by
  unfold tailWord_3081549
  simp only [CollatzResearch.WordTrace]
  refine ⟨112393325513081734514487701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74928883675387823009658467 112393325513081734514487701)
  ·
    refine ⟨5268437133425706305366611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112393325513081734514487701 5268437133425706305366611)
    ·
      refine ⟨7902655700138559458049917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268437133425706305366611 7902655700138559458049917)
      ·
        refine ⟨2963495887551959796768719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7902655700138559458049917 2963495887551959796768719)
        ·
          refine ⟨4445243831327939695153079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963495887551959796768719 4445243831327939695153079)
          ·
            refine ⟨6667865746991909542729619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445243831327939695153079 6667865746991909542729619)
            ·
              refine ⟨10001798620487864314094429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667865746991909542729619 10001798620487864314094429)
              ·
                refine ⟨3750674482682949117785411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10001798620487864314094429 3750674482682949117785411)
                ·
                  refine ⟨5626011724024423676678117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750674482682949117785411 5626011724024423676678117)
                  ·
                    refine ⟨1054877198254579439377147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626011724024423676678117 1054877198254579439377147)
                    ·
                      rfl

theorem cell22_3081549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3081549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081549 prefixEnd_3081549 := by exact prefixLift 3081549
  have htrace : WordTrace (prefixWord ++ tailWord_3081549) baseStart_3081549 baseEnd_3081549 := by
    simpa [prefixWord, tailWord_3081549, baseEnd_3081549] using wordTrace_append hprefix tailTrace_3081549
  have hstable : (prefixWord ++ tailWord_3081549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081549).length < 2 ^ (prefixWord ++ tailWord_3081549).sum := by decide
  have hdescent : baseEnd_3081549 < baseStart_3081549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081598 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3081598 : Nat := 118140960795 + 3081598 * 2 ^ 59
def prefixEnd_3081598 : Nat := 4983230072969 + 3 ^ 40 * 3081598 * 2
def baseEnd_3081598 : Nat := 351631323985319881633999

theorem tailTrace_3081598 : CollatzResearch.WordTrace tailWord_3081598 prefixEnd_3081598 351631323985319881633999 := by
  unfold tailWord_3081598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14049389086238026985377681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74930075126602810588680965 14049389086238026985377681)
  ·
    refine ⟨10537041814678520239033261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14049389086238026985377681 10537041814678520239033261)
    ·
      refine ⟨3951390680504445089637473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10537041814678520239033261 3951390680504445089637473)
      ·
        refine ⟨2963543010378333817228105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3951390680504445089637473 2963543010378333817228105)
        ·
          refine ⟨2222657257783750362921079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963543010378333817228105 2222657257783750362921079)
          ·
            refine ⟨3333985886675625544381619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222657257783750362921079 3333985886675625544381619)
            ·
              refine ⟨5000978830013438316572429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333985886675625544381619 5000978830013438316572429)
              ·
                refine ⟨1875367061255039368714661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000978830013438316572429 1875367061255039368714661)
                ·
                  refine ⟨351631323985319881633999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875367061255039368714661 351631323985319881633999)
                  ·
                    rfl

theorem cell22_3081598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3081598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081598 prefixEnd_3081598 := by exact prefixLift 3081598
  have htrace : WordTrace (prefixWord ++ tailWord_3081598) baseStart_3081598 baseEnd_3081598 := by
    simpa [prefixWord, tailWord_3081598, baseEnd_3081598] using wordTrace_append hprefix tailTrace_3081598
  have hstable : (prefixWord ++ tailWord_3081598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081598).length < 2 ^ (prefixWord ++ tailWord_3081598).sum := by decide
  have hdescent : baseEnd_3081598 < baseStart_3081598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081603 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 7]
def baseStart_3081603 : Nat := 118140960795 + 3081603 * 2 ^ 59
def prefixEnd_3081603 : Nat := 4983230072969 + 3 ^ 40 * 3081603 * 2
def baseEnd_3081603 : Nat := 351631894519380432842327

theorem tailTrace_3081603 : CollatzResearch.WordTrace tailWord_3081603 prefixEnd_3081603 351631894519380432842327 := by
  unfold tailWord_3081603
  simp only [CollatzResearch.WordTrace]
  refine ⟨112395295054886101736953463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74930196703257401157968975 112395295054886101736953463)
  ·
    refine ⟨168592942582329152605430195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112395295054886101736953463 168592942582329152605430195)
    ·
      refine ⟨252889413873493728908145293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168592942582329152605430195 252889413873493728908145293)
      ·
        refine ⟨94833530202560148340554485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252889413873493728908145293 94833530202560148340554485)
        ·
          refine ⟨8890643456490013906926983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94833530202560148340554485 8890643456490013906926983)
          ·
            refine ⟨13335965184735020860390475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890643456490013906926983 13335965184735020860390475)
            ·
              refine ⟨20003947777102531290585713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13335965184735020860390475 20003947777102531290585713)
              ·
                refine ⟨15002960832826898467939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20003947777102531290585713 15002960832826898467939285)
                ·
                  refine ⟨351631894519380432842327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15002960832826898467939285 351631894519380432842327)
                  ·
                    rfl

theorem cell22_3081603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_3081603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081603 prefixEnd_3081603 := by exact prefixLift 3081603
  have htrace : WordTrace (prefixWord ++ tailWord_3081603) baseStart_3081603 baseEnd_3081603 := by
    simpa [prefixWord, tailWord_3081603, baseEnd_3081603] using wordTrace_append hprefix tailTrace_3081603
  have hstable : (prefixWord ++ tailWord_3081603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081603).length < 2 ^ (prefixWord ++ tailWord_3081603).sum := by decide
  have hdescent : baseEnd_3081603 < baseStart_3081603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081620 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3081620 : Nat := 118140960795 + 3081620 * 2 ^ 59
def prefixEnd_3081620 : Nat := 4983230072969 + 3 ^ 40 * 3081620 * 2
def baseEnd_3081620 : Nat := 351633834335186306950643

theorem tailTrace_3081620 : CollatzResearch.WordTrace tailWord_3081620 prefixEnd_3081620 351633834335186306950643 := by
  unfold tailWord_3081620
  simp only [CollatzResearch.WordTrace]
  refine ⟨56197957547912256820161157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74930610063883009093548209 56197957547912256820161157)
  ·
    refine ⟨10537117040233548153780217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56197957547912256820161157 10537117040233548153780217)
    ·
      refine ⟨7902837780175161115335163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10537117040233548153780217 7902837780175161115335163)
      ·
        refine ⟨11854256670262741673002745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902837780175161115335163 11854256670262741673002745)
        ·
          refine ⟨8890692502697056254752059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11854256670262741673002745 8890692502697056254752059)
          ·
            refine ⟨13336038754045584382128089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890692502697056254752059 13336038754045584382128089)
            ·
              refine ⟨10002029065534188286596067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13336038754045584382128089 10002029065534188286596067)
              ·
                refine ⟨15003043598301282429894101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10002029065534188286596067 15003043598301282429894101)
                ·
                  refine ⟨351633834335186306950643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15003043598301282429894101 351633834335186306950643)
                  ·
                    rfl

theorem cell22_3081620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3081620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081620 prefixEnd_3081620 := by exact prefixLift 3081620
  have htrace : WordTrace (prefixWord ++ tailWord_3081620) baseStart_3081620 baseEnd_3081620 := by
    simpa [prefixWord, tailWord_3081620, baseEnd_3081620] using wordTrace_append hprefix tailTrace_3081620
  have hstable : (prefixWord ++ tailWord_3081620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081620).length < 2 ^ (prefixWord ++ tailWord_3081620).sum := by decide
  have hdescent : baseEnd_3081620 < baseStart_3081620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081624 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_3081624 : Nat := 118140960795 + 3081624 * 2 ^ 59
def prefixEnd_3081624 : Nat := 4983230072969 + 3 ^ 40 * 3081624 * 2
def baseEnd_3081624 : Nat := 1054902872287304243751917

theorem tailTrace_3081624 : CollatzResearch.WordTrace tailWord_3081624 prefixEnd_3081624 1054902872287304243751917 := by
  unfold tailWord_3081624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56198030493905011161733963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74930707325206681548978617 56198030493905011161733963)
  ·
    refine ⟨84297045740857516742600945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56198030493905011161733963 84297045740857516742600945)
    ·
      refine ⟨63222784305643137556950709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84297045740857516742600945 63222784305643137556950709)
      ·
        refine ⟨5927136028654044145964129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63222784305643137556950709 5927136028654044145964129)
        ·
          refine ⟨4445352021490533109473097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5927136028654044145964129 4445352021490533109473097)
          ·
            refine ⟨3334014016117899832104823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4445352021490533109473097 3334014016117899832104823)
            ·
              refine ⟨5001021024176849748157235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334014016117899832104823 5001021024176849748157235)
              ·
                refine ⟨7501531536265274622235853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001021024176849748157235 7501531536265274622235853)
                ·
                  refine ⟨2813074326099477983338445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7501531536265274622235853 2813074326099477983338445)
                  ·
                    refine ⟨1054902872287304243751917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813074326099477983338445 1054902872287304243751917)
                    ·
                      rfl

theorem cell22_3081624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_3081624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081624 prefixEnd_3081624 := by exact prefixLift 3081624
  have htrace : WordTrace (prefixWord ++ tailWord_3081624) baseStart_3081624 baseEnd_3081624 := by
    simpa [prefixWord, tailWord_3081624, baseEnd_3081624] using wordTrace_append hprefix tailTrace_3081624
  have hstable : (prefixWord ++ tailWord_3081624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081624).length < 2 ^ (prefixWord ++ tailWord_3081624).sum := by decide
  have hdescent : baseEnd_3081624 < baseStart_3081624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081650 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3081650 : Nat := 118140960795 + 3081650 * 2 ^ 59
def prefixEnd_3081650 : Nat := 4983230072969 + 3 ^ 40 * 3081650 * 2
def baseEnd_3081650 : Nat := 1054911772618648842601837

theorem tailTrace_3081650 : CollatzResearch.WordTrace tailWord_3081650 prefixEnd_3081650 1054911772618648842601837 := by
  unfold tailWord_3081650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28099252321428957190978601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74931339523810552509276269 28099252321428957190978601)
  ·
    refine ⟨21074439241071717893233951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28099252321428957190978601 21074439241071717893233951)
    ·
      refine ⟨31611658861607576839850927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21074439241071717893233951 31611658861607576839850927)
      ·
        refine ⟨47417488292411365259776391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31611658861607576839850927 47417488292411365259776391)
        ·
          refine ⟨71126232438617047889664587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47417488292411365259776391 71126232438617047889664587)
          ·
            refine ⟨106689348657925571834496881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71126232438617047889664587 106689348657925571834496881)
            ·
              refine ⟨80017011493444178875872661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106689348657925571834496881 80017011493444178875872661)
              ·
                refine ⟨3750797413755195884806531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80017011493444178875872661 3750797413755195884806531)
                ·
                  refine ⟨5626196120632793827209797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750797413755195884806531 5626196120632793827209797)
                  ·
                    refine ⟨1054911772618648842601837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626196120632793827209797 1054911772618648842601837)
                    ·
                      rfl

theorem cell22_3081650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3081650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081650 prefixEnd_3081650 := by exact prefixLift 3081650
  have htrace : WordTrace (prefixWord ++ tailWord_3081650) baseStart_3081650 baseEnd_3081650 := by
    simpa [prefixWord, tailWord_3081650, baseEnd_3081650] using wordTrace_append hprefix tailTrace_3081650
  have hstable : (prefixWord ++ tailWord_3081650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081650).length < 2 ^ (prefixWord ++ tailWord_3081650).sum := by decide
  have hdescent : baseEnd_3081650 < baseStart_3081650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081697 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_3081697 : Nat := 118140960795 + 3081697 * 2 ^ 59
def prefixEnd_3081697 : Nat := 4983230072969 + 3 ^ 40 * 3081697 * 2
def baseEnd_3081697 : Nat := 1054927861679156386676693

theorem tailTrace_3081697 : CollatzResearch.WordTrace tailWord_3081697 prefixEnd_3081697 1054927861679156386676693 := by
  unfold tailWord_3081697
  simp only [CollatzResearch.WordTrace]
  refine ⟨112398723516545555790875345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74932482344363703860583563 112398723516545555790875345)
  ·
    refine ⟨84299042637409166843156509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112398723516545555790875345 84299042637409166843156509)
    ·
      refine ⟨31612140989028437566183691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84299042637409166843156509 31612140989028437566183691)
      ·
        refine ⟨47418211483542656349275537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31612140989028437566183691 47418211483542656349275537)
        ·
          refine ⟨35563658612656992261956653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47418211483542656349275537 35563658612656992261956653)
          ·
            refine ⟨13336371979746372098233745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35563658612656992261956653 13336371979746372098233745)
            ·
              refine ⟨10002278984809779073675309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13336371979746372098233745 10002278984809779073675309)
              ·
                refine ⟨3750854619303667152628241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10002278984809779073675309 3750854619303667152628241)
                ·
                  refine ⟨2813140964477750364471181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750854619303667152628241 2813140964477750364471181)
                  ·
                    refine ⟨1054927861679156386676693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813140964477750364471181 1054927861679156386676693)
                    ·
                      rfl

theorem cell22_3081697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_3081697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081697 prefixEnd_3081697 := by exact prefixLift 3081697
  have htrace : WordTrace (prefixWord ++ tailWord_3081697) baseStart_3081697 baseEnd_3081697 := by
    simpa [prefixWord, tailWord_3081697, baseEnd_3081697] using wordTrace_append hprefix tailTrace_3081697
  have hstable : (prefixWord ++ tailWord_3081697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081697).length < 2 ^ (prefixWord ++ tailWord_3081697).sum := by decide
  have hdescent : baseEnd_3081697 < baseStart_3081697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081708 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_3081708 : Nat := 118140960795 + 3081708 * 2 ^ 59
def prefixEnd_3081708 : Nat := 4983230072969 + 3 ^ 40 * 3081708 * 2
def baseEnd_3081708 : Nat := 1054931627203956024651659

theorem tailTrace_3081708 : CollatzResearch.WordTrace tailWord_3081708 prefixEnd_3081708 1054931627203956024651659 := by
  unfold tailWord_3081708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56199562359752852334762889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74932749813003803113017185 56199562359752852334762889)
  ·
    refine ⟨42149671769814639251072167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56199562359752852334762889 42149671769814639251072167)
    ·
      refine ⟨63224507654721958876608251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42149671769814639251072167 63224507654721958876608251)
      ·
        refine ⟨94836761482082938314912377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63224507654721958876608251 94836761482082938314912377)
        ·
          refine ⟨71127571111562203736184283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94836761482082938314912377 71127571111562203736184283)
          ·
            refine ⟨106691356667343305604276425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71127571111562203736184283 106691356667343305604276425)
            ·
              refine ⟨80018517500507479203207319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106691356667343305604276425 80018517500507479203207319)
              ·
                refine ⟨120027776250761218804810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80018517500507479203207319 120027776250761218804810979)
                ·
                  refine ⟨180041664376141828207216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120027776250761218804810979 180041664376141828207216469)
                  ·
                    refine ⟨1054931627203956024651659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180041664376141828207216469 1054931627203956024651659)
                    ·
                      rfl

theorem cell22_3081708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_3081708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081708 prefixEnd_3081708 := by exact prefixLift 3081708
  have htrace : WordTrace (prefixWord ++ tailWord_3081708) baseStart_3081708 baseEnd_3081708 := by
    simpa [prefixWord, tailWord_3081708, baseEnd_3081708] using wordTrace_append hprefix tailTrace_3081708
  have hstable : (prefixWord ++ tailWord_3081708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081708).length < 2 ^ (prefixWord ++ tailWord_3081708).sum := by decide
  have hdescent : baseEnd_3081708 < baseStart_3081708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081712 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_3081712 : Nat := 118140960795 + 3081712 * 2 ^ 59
def prefixEnd_3081712 : Nat := 4983230072969 + 3 ^ 40 * 3081712 * 2
def baseEnd_3081712 : Nat := 1054932996485701347551647

theorem tailTrace_3081712 : CollatzResearch.WordTrace tailWord_3081712 prefixEnd_3081712 1054932996485701347551647 := by
  unfold tailWord_3081712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56199635305745606676335695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74932847074327475568447593 56199635305745606676335695)
  ·
    refine ⟨84299452958618410014503543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56199635305745606676335695 84299452958618410014503543)
    ·
      refine ⟨126449179437927615021755315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84299452958618410014503543 126449179437927615021755315)
      ·
        refine ⟨189673769156891422532632973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126449179437927615021755315 189673769156891422532632973)
        ·
          refine ⟨71127663433834283449737365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189673769156891422532632973 71127663433834283449737365)
          ·
            refine ⟨3334109223460982036706439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71127663433834283449737365 3334109223460982036706439)
            ·
              refine ⟨5001163835191473055059659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334109223460982036706439 5001163835191473055059659)
              ·
                refine ⟨7501745752787209582589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001163835191473055059659 7501745752787209582589489)
                ·
                  refine ⟨5626309314590407186942117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7501745752787209582589489 5626309314590407186942117)
                  ·
                    refine ⟨1054932996485701347551647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626309314590407186942117 1054932996485701347551647)
                    ·
                      rfl

theorem cell22_3081712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_3081712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081712 prefixEnd_3081712 := by exact prefixLift 3081712
  have htrace : WordTrace (prefixWord ++ tailWord_3081712) baseStart_3081712 baseEnd_3081712 := by
    simpa [prefixWord, tailWord_3081712, baseEnd_3081712] using wordTrace_append hprefix tailTrace_3081712
  have hstable : (prefixWord ++ tailWord_3081712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081712).length < 2 ^ (prefixWord ++ tailWord_3081712).sum := by decide
  have hdescent : baseEnd_3081712 < baseStart_3081712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081723 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_3081723 : Nat := 118140960795 + 3081723 * 2 ^ 59
def prefixEnd_3081723 : Nat := 4983230072969 + 3 ^ 40 * 3081723 * 2
def baseEnd_3081723 : Nat := 1054936762010500985526613

theorem tailTrace_3081723 : CollatzResearch.WordTrace tailWord_3081723 prefixEnd_3081723 1054936762010500985526613 := by
  unfold tailWord_3081723
  simp only [CollatzResearch.WordTrace]
  refine ⟨112399671814451362231321823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74933114542967574820881215 112399671814451362231321823)
  ·
    refine ⟨168599507721677043346982735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112399671814451362231321823 168599507721677043346982735)
    ·
      refine ⟨252899261582515565020474103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168599507721677043346982735 252899261582515565020474103)
      ·
        refine ⟨379348892373773347530711155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252899261582515565020474103 379348892373773347530711155)
        ·
          refine ⟨569023338560660021296066733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379348892373773347530711155 569023338560660021296066733)
          ·
            refine ⟨213383751960247507986025025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569023338560660021296066733 213383751960247507986025025)
            ·
              refine ⟨160037813970185630989518769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213383751960247507986025025 160037813970185630989518769)
              ·
                refine ⟨120028360477639223242139077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160037813970185630989518769 120028360477639223242139077)
                ·
                  refine ⟨22505317589557354357901077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120028360477639223242139077 22505317589557354357901077)
                  ·
                    refine ⟨1054936762010500985526613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22505317589557354357901077 1054936762010500985526613)
                    ·
                      rfl

theorem cell22_3081723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_3081723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081723 prefixEnd_3081723 := by exact prefixLift 3081723
  have htrace : WordTrace (prefixWord ++ tailWord_3081723) baseStart_3081723 baseEnd_3081723 := by
    simpa [prefixWord, tailWord_3081723, baseEnd_3081723] using wordTrace_append hprefix tailTrace_3081723
  have hstable : (prefixWord ++ tailWord_3081723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081723).length < 2 ^ (prefixWord ++ tailWord_3081723).sum := by decide
  have hdescent : baseEnd_3081723 < baseStart_3081723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081748 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3081748 : Nat := 118140960795 + 3081748 * 2 ^ 59
def prefixEnd_3081748 : Nat := 4983230072969 + 3 ^ 40 * 3081748 * 2
def baseEnd_3081748 : Nat := 1054945320021409253651537

theorem tailTrace_3081748 : CollatzResearch.WordTrace tailWord_3081748 prefixEnd_3081748 1054945320021409253651537 := by
  unfold tailWord_3081748
  simp only [CollatzResearch.WordTrace]
  refine ⟨56200291819680395750490949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74933722426240527667321265 56200291819680395750490949)
  ·
    refine ⟨10537554716190074203217053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56200291819680395750490949 10537554716190074203217053)
    ·
      refine ⟨3951583018571277826206395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10537554716190074203217053 3951583018571277826206395)
      ·
        refine ⟨5927374527856916739309593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951583018571277826206395 5927374527856916739309593)
        ·
          refine ⟨4445530895892687554482195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5927374527856916739309593 4445530895892687554482195)
          ·
            refine ⟨6668296343839031331723293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445530895892687554482195 6668296343839031331723293)
            ·
              refine ⟨2500611128939636749396235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6668296343839031331723293 2500611128939636749396235)
              ·
                refine ⟨3750916693409455124094353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500611128939636749396235 3750916693409455124094353)
                ·
                  refine ⟨2813187520057091343070765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750916693409455124094353 2813187520057091343070765)
                  ·
                    refine ⟨1054945320021409253651537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813187520057091343070765 1054945320021409253651537)
                    ·
                      rfl

theorem cell22_3081748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3081748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081748 prefixEnd_3081748 := by exact prefixLift 3081748
  have htrace : WordTrace (prefixWord ++ tailWord_3081748) baseStart_3081748 baseEnd_3081748 := by
    simpa [prefixWord, tailWord_3081748, baseEnd_3081748] using wordTrace_append hprefix tailTrace_3081748
  have hstable : (prefixWord ++ tailWord_3081748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081748).length < 2 ^ (prefixWord ++ tailWord_3081748).sum := by decide
  have hdescent : baseEnd_3081748 < baseStart_3081748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081832 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3081832 : Nat := 118140960795 + 3081832 * 2 ^ 59
def prefixEnd_3081832 : Nat := 4983230072969 + 3 ^ 40 * 3081832 * 2
def baseEnd_3081832 : Nat := 1054974074938061034551279

theorem tailTrace_3081832 : CollatzResearch.WordTrace tailWord_3081832 prefixEnd_3081832 1054974074938061034551279 := by
  unfold tailWord_3081832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201823685528236923519875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74935764914037649231359833 56201823685528236923519875)
  ·
    refine ⟨84302735528292355385279813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56201823685528236923519875 84302735528292355385279813)
    ·
      refine ⟨15806762911554816634739965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84302735528292355385279813 15806762911554816634739965)
      ·
        refine ⟨5927536091833056238027487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15806762911554816634739965 5927536091833056238027487)
        ·
          refine ⟨8891304137749584357041231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927536091833056238027487 8891304137749584357041231)
          ·
            refine ⟨13336956206624376535561847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891304137749584357041231 13336956206624376535561847)
            ·
              refine ⟨20005434309936564803342771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336956206624376535561847 20005434309936564803342771)
              ·
                refine ⟨30008151464904847205014157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20005434309936564803342771 30008151464904847205014157)
                ·
                  refine ⟨11253056799339317701880309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30008151464904847205014157 11253056799339317701880309)
                  ·
                    refine ⟨1054974074938061034551279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11253056799339317701880309 1054974074938061034551279)
                    ·
                      rfl

theorem cell22_3081832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3081832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081832 prefixEnd_3081832 := by exact prefixLift 3081832
  have htrace : WordTrace (prefixWord ++ tailWord_3081832) baseStart_3081832 baseEnd_3081832 := by
    simpa [prefixWord, tailWord_3081832, baseEnd_3081832] using wordTrace_append hprefix tailTrace_3081832
  have hstable : (prefixWord ++ tailWord_3081832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081832).length < 2 ^ (prefixWord ++ tailWord_3081832).sum := by decide
  have hdescent : baseEnd_3081832 < baseStart_3081832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081849 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_3081849 : Nat := 118140960795 + 3081849 * 2 ^ 59
def prefixEnd_3081849 : Nat := 4983230072969 + 3 ^ 40 * 3081849 * 2
def baseEnd_3081849 : Nat := 1054979894385478656876227

theorem tailTrace_3081849 : CollatzResearch.WordTrace tailWord_3081849 prefixEnd_3081849 1054979894385478656876227 := by
  unfold tailWord_3081849
  simp only [CollatzResearch.WordTrace]
  refine ⟨112404267411994885750408601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74936178274663257166939067 112404267411994885750408601)
  ·
    refine ⟨84303200558996164312806451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112404267411994885750408601 84303200558996164312806451)
    ·
      refine ⟨126454800838494246469209677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84303200558996164312806451 126454800838494246469209677)
      ·
        refine ⟨47420550314435342425953629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126454800838494246469209677 47420550314435342425953629)
        ·
          refine ⟨17782706367913253409732611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47420550314435342425953629 17782706367913253409732611)
          ·
            refine ⟨26674059551869880114598917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17782706367913253409732611 26674059551869880114598917)
            ·
              refine ⟨5001386165975602521487297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26674059551869880114598917 5001386165975602521487297)
              ·
                refine ⟨3751039624481701891115473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001386165975602521487297 3751039624481701891115473)
                ·
                  refine ⟨2813279718361276418336605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3751039624481701891115473 2813279718361276418336605)
                  ·
                    refine ⟨1054979894385478656876227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813279718361276418336605 1054979894385478656876227)
                    ·
                      rfl

theorem cell22_3081849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_3081849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081849 prefixEnd_3081849 := by exact prefixLift 3081849
  have htrace : WordTrace (prefixWord ++ tailWord_3081849) baseStart_3081849 baseEnd_3081849 := by
    simpa [prefixWord, tailWord_3081849, baseEnd_3081849] using wordTrace_append hprefix tailTrace_3081849
  have hstable : (prefixWord ++ tailWord_3081849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081849).length < 2 ^ (prefixWord ++ tailWord_3081849).sum := by decide
  have hdescent : baseEnd_3081849 < baseStart_3081849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081896 : List Nat := [2, 1, 7, 1, 1, 1, 9]
def baseStart_3081896 : Nat := 118140960795 + 3081896 * 2 ^ 59
def prefixEnd_3081896 : Nat := 4983230072969 + 3 ^ 40 * 3081896 * 2
def baseEnd_3081896 : Nat := 39073925312814303738929

theorem tailTrace_3081896 : CollatzResearch.WordTrace tailWord_3081896 prefixEnd_3081896 39073925312814303738929 := by
  unfold tailWord_3081896
  simp only [CollatzResearch.WordTrace]
  refine ⟨56202990821412306388684771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74937321095216408518246361 56202990821412306388684771)
  ·
    refine ⟨84304486232118459583027157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56202990821412306388684771 84304486232118459583027157)
    ·
      refine ⟨1975886396065276396477199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84304486232118459583027157 1975886396065276396477199)
      ·
        refine ⟨2963829594097914594715799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975886396065276396477199 2963829594097914594715799)
        ·
          refine ⟨4445744391146871892073699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963829594097914594715799 4445744391146871892073699)
          ·
            refine ⟨6668616586720307838110549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445744391146871892073699 6668616586720307838110549)
            ·
              refine ⟨39073925312814303738929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6668616586720307838110549 39073925312814303738929)
              ·
                rfl

theorem cell22_3081896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 9].length) (baseStart_3081896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081896 prefixEnd_3081896 := by exact prefixLift 3081896
  have htrace : WordTrace (prefixWord ++ tailWord_3081896) baseStart_3081896 baseEnd_3081896 := by
    simpa [prefixWord, tailWord_3081896, baseEnd_3081896] using wordTrace_append hprefix tailTrace_3081896
  have hstable : (prefixWord ++ tailWord_3081896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081896).length < 2 ^ (prefixWord ++ tailWord_3081896).sum := by decide
  have hdescent : baseEnd_3081896 < baseStart_3081896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081911 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 1, 3]
def baseStart_3081911 : Nat := 118140960795 + 3081911 * 2 ^ 59
def prefixEnd_3081911 : Nat := 4983230072969 + 3 ^ 40 * 3081911 * 2
def baseEnd_3081911 : Nat := 1055001118252531161826037

theorem tailTrace_3081911 : CollatzResearch.WordTrace tailWord_3081911 prefixEnd_3081911 1055001118252531161826037 := by
  unfold tailWord_3081911
  simp only [CollatzResearch.WordTrace]
  refine ⟨112406528737770270339165587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74937685825180180226110391 112406528737770270339165587)
  ·
    refine ⟨168609793106655405508748381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112406528737770270339165587 168609793106655405508748381)
    ·
      refine ⟨63228672414995777065780643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168609793106655405508748381 63228672414995777065780643)
      ·
        refine ⟨94843008622493665598670965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63228672414995777065780643 94843008622493665598670965)
        ·
          refine ⟨8891532058358781149875403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94843008622493665598670965 8891532058358781149875403)
          ·
            refine ⟨13337298087538171724813105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891532058358781149875403 13337298087538171724813105)
            ·
              refine ⟨10002973565653628793609829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13337298087538171724813105 10002973565653628793609829)
              ·
                refine ⟨1875557543560055398801843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10002973565653628793609829 1875557543560055398801843)
                ·
                  refine ⟨2813336315340083098202765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875557543560055398801843 2813336315340083098202765)
                  ·
                    refine ⟨1055001118252531161826037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813336315340083098202765 1055001118252531161826037)
                    ·
                      rfl

theorem cell22_3081911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_3081911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081911 prefixEnd_3081911 := by exact prefixLift 3081911
  have htrace : WordTrace (prefixWord ++ tailWord_3081911) baseStart_3081911 baseEnd_3081911 := by
    simpa [prefixWord, tailWord_3081911, baseEnd_3081911] using wordTrace_append hprefix tailTrace_3081911
  have hstable : (prefixWord ++ tailWord_3081911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081911).length < 2 ^ (prefixWord ++ tailWord_3081911).sum := by decide
  have hdescent : baseEnd_3081911 < baseStart_3081911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081969 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 6]
def baseStart_3081969 : Nat := 118140960795 + 3081969 * 2 ^ 59
def prefixEnd_3081969 : Nat := 4983230072969 + 3 ^ 40 * 3081969 * 2
def baseEnd_3081969 : Nat := 351673657612612781291953

theorem tailTrace_3081969 : CollatzResearch.WordTrace tailWord_3081969 prefixEnd_3081969 351673657612612781291953 := by
  unfold tailWord_3081969
  simp only [CollatzResearch.WordTrace]
  refine ⟨112408644171560146244776961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74939096114373430829851307 112408644171560146244776961)
  ·
    refine ⟨84306483128670109683582721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112408644171560146244776961 84306483128670109683582721)
    ·
      refine ⟨63229862346502582262687041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84306483128670109683582721 63229862346502582262687041)
      ·
        refine ⟨47422396759876936697015281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63229862346502582262687041 47422396759876936697015281)
        ·
          refine ⟨35566797569907702522761461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47422396759876936697015281 35566797569907702522761461)
          ·
            refine ⟨3334387272178847111508887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35566797569907702522761461 3334387272178847111508887)
            ·
              refine ⟨5001580908268270667263331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334387272178847111508887 5001580908268270667263331)
              ·
                refine ⟨7502371362402406000894997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001580908268270667263331 7502371362402406000894997)
                ·
                  refine ⟨351673657612612781291953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7502371362402406000894997 351673657612612781291953)
                  ·
                    rfl

theorem cell22_3081969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_3081969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081969 prefixEnd_3081969 := by exact prefixLift 3081969
  have htrace : WordTrace (prefixWord ++ tailWord_3081969) baseStart_3081969 baseEnd_3081969 := by
    simpa [prefixWord, tailWord_3081969, baseEnd_3081969] using wordTrace_append hprefix tailTrace_3081969
  have hstable : (prefixWord ++ tailWord_3081969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081969).length < 2 ^ (prefixWord ++ tailWord_3081969).sum := by decide
  have hdescent : baseEnd_3081969 < baseStart_3081969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081984 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_3081984 : Nat := 118140960795 + 3081984 * 2 ^ 59
def prefixEnd_3081984 : Nat := 4983230072969 + 3 ^ 40 * 3081984 * 2
def baseEnd_3081984 : Nat := 1055026107644383304750813

theorem tailTrace_3081984 : CollatzResearch.WordTrace tailWord_3081984 prefixEnd_3081984 1055026107644383304750813 := by
  unfold tailWord_3081984
  simp only [CollatzResearch.WordTrace]
  refine ⟨56204595633252901903286503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74939460844337202537715337 56204595633252901903286503)
  ·
    refine ⟨84306893449879352854929755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56204595633252901903286503 84306893449879352854929755)
    ·
      refine ⟨126460340174819029282394633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84306893449879352854929755 126460340174819029282394633)
      ·
        refine ⟨94845255131114271961795975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126460340174819029282394633 94845255131114271961795975)
        ·
          refine ⟨142267882696671407942693963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94845255131114271961795975 142267882696671407942693963)
          ·
            refine ⟨213401824045007111914040945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142267882696671407942693963 213401824045007111914040945)
            ·
              refine ⟨160051368033755333935530709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213401824045007111914040945 160051368033755333935530709)
              ·
                refine ⟨3751203938291140639114001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160051368033755333935530709 3751203938291140639114001)
                ·
                  refine ⟨2813402953718355479335501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3751203938291140639114001 2813402953718355479335501)
                  ·
                    refine ⟨1055026107644383304750813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813402953718355479335501 1055026107644383304750813)
                    ·
                      rfl

theorem cell22_3081984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_3081984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3081984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3081984 prefixEnd_3081984 := by exact prefixLift 3081984
  have htrace : WordTrace (prefixWord ++ tailWord_3081984) baseStart_3081984 baseEnd_3081984 := by
    simpa [prefixWord, tailWord_3081984, baseEnd_3081984] using wordTrace_append hprefix tailTrace_3081984
  have hstable : (prefixWord ++ tailWord_3081984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081984).length < 2 ^ (prefixWord ++ tailWord_3081984).sum := by decide
  have hdescent : baseEnd_3081984 < baseStart_3081984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082046 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3082046 : Nat := 118140960795 + 3082046 * 2 ^ 59
def prefixEnd_3082046 : Nat := 4983230072969 + 3 ^ 40 * 3082046 * 2
def baseEnd_3082046 : Nat := 1055047331511435809700623

theorem tailTrace_3082046 : CollatzResearch.WordTrace tailWord_3082046 prefixEnd_3082046 1055047331511435809700623 := by
  unfold tailWord_3082046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051431574035148549416249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74940968394854125596886661 14051431574035148549416249)
  ·
    refine ⟨10538573680526361412062187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14051431574035148549416249 10538573680526361412062187)
    ·
      refine ⟨15807860520789542118093281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10538573680526361412062187 15807860520789542118093281)
      ·
        refine ⟨11855895390592156588569961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15807860520789542118093281 11855895390592156588569961)
        ·
          refine ⟨8891921542944117441427471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11855895390592156588569961 8891921542944117441427471)
          ·
            refine ⟨13337882314416176162141207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891921542944117441427471 13337882314416176162141207)
            ·
              refine ⟨20006823471624264243211811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337882314416176162141207 20006823471624264243211811)
              ·
                refine ⟨30010235207436396364817717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20006823471624264243211811 30010235207436396364817717)
                ·
                  refine ⟨2813459550697162159201661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30010235207436396364817717 2813459550697162159201661)
                  ·
                    refine ⟨1055047331511435809700623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813459550697162159201661 1055047331511435809700623)
                    ·
                      rfl

theorem cell22_3082046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3082046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082046 prefixEnd_3082046 := by exact prefixLift 3082046
  have htrace : WordTrace (prefixWord ++ tailWord_3082046) baseStart_3082046 baseEnd_3082046 := by
    simpa [prefixWord, tailWord_3082046, baseEnd_3082046] using wordTrace_append hprefix tailTrace_3082046
  have hstable : (prefixWord ++ tailWord_3082046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082046).length < 2 ^ (prefixWord ++ tailWord_3082046).sum := by decide
  have hdescent : baseEnd_3082046 < baseStart_3082046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082057 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_3082057 : Nat := 118140960795 + 3082057 * 2 ^ 59
def prefixEnd_3082057 : Nat := 4983230072969 + 3 ^ 40 * 3082057 * 2
def baseEnd_3082057 : Nat := 1055051097036235447675589

theorem tailTrace_3082057 : CollatzResearch.WordTrace tailWord_3082057 prefixEnd_3082057 1055051097036235447675589 := by
  unfold tailWord_3082057
  simp only [CollatzResearch.WordTrace]
  refine ⟨112411853795241337273980425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74941235863494224849320283 112411853795241337273980425)
  ·
    refine ⟨84308890346431002955485319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112411853795241337273980425 84308890346431002955485319)
    ·
      refine ⟨126463335519646504433227979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84308890346431002955485319 126463335519646504433227979)
      ·
        refine ⟨189695003279469756649841969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126463335519646504433227979 189695003279469756649841969)
        ·
          refine ⟨142271252459602317487381477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189695003279469756649841969 142271252459602317487381477)
          ·
            refine ⟨26675859836175434528884027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142271252459602317487381477 26675859836175434528884027)
            ·
              refine ⟨40013789754263151793326041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26675859836175434528884027 40013789754263151793326041)
              ·
                refine ⟨30010342315697363844994531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40013789754263151793326041 30010342315697363844994531)
                ·
                  refine ⟨45015513473546045767491797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30010342315697363844994531 45015513473546045767491797)
                  ·
                    refine ⟨1055051097036235447675589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45015513473546045767491797 1055051097036235447675589)
                    ·
                      rfl

theorem cell22_3082057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_3082057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082057 prefixEnd_3082057 := by exact prefixLift 3082057
  have htrace : WordTrace (prefixWord ++ tailWord_3082057) baseStart_3082057 baseEnd_3082057 := by
    simpa [prefixWord, tailWord_3082057, baseEnd_3082057] using wordTrace_append hprefix tailTrace_3082057
  have hstable : (prefixWord ++ tailWord_3082057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082057).length < 2 ^ (prefixWord ++ tailWord_3082057).sum := by decide
  have hdescent : baseEnd_3082057 < baseStart_3082057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082076 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_3082076 : Nat := 118140960795 + 3082076 * 2 ^ 59
def prefixEnd_3082076 : Nat := 4983230072969 + 3 ^ 40 * 3082076 * 2
def baseEnd_3082076 : Nat := 351685867041508577150177

theorem tailTrace_3082076 : CollatzResearch.WordTrace tailWord_3082076 prefixEnd_3082076 351685867041508577150177 := by
  unfold tailWord_3082076
  simp only [CollatzResearch.WordTrace]
  refine ⟨56206273391086251759461041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74941697854781669012614721 56206273391086251759461041)
  ·
    refine ⟨42154705043314688819595781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56206273391086251759461041 42154705043314688819595781)
    ·
      refine ⟨7904007195621504153674209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42154705043314688819595781 7904007195621504153674209)
      ·
        refine ⟨5928005396716128115255657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904007195621504153674209 5928005396716128115255657)
        ·
          refine ⟨4446004047537096086441743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5928005396716128115255657 4446004047537096086441743)
          ·
            refine ⟨6669006071305644129662615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446004047537096086441743 6669006071305644129662615)
            ·
              refine ⟨10003509106958466194493923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669006071305644129662615 10003509106958466194493923)
              ·
                refine ⟨15005263660437699291740885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003509106958466194493923 15005263660437699291740885)
                ·
                  refine ⟨351685867041508577150177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15005263660437699291740885 351685867041508577150177)
                  ·
                    rfl

theorem cell22_3082076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_3082076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082076 prefixEnd_3082076 := by exact prefixLift 3082076
  have htrace : WordTrace (prefixWord ++ tailWord_3082076) baseStart_3082076 baseEnd_3082076 := by
    simpa [prefixWord, tailWord_3082076, baseEnd_3082076] using wordTrace_append hprefix tailTrace_3082076
  have hstable : (prefixWord ++ tailWord_3082076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082076).length < 2 ^ (prefixWord ++ tailWord_3082076).sum := by decide
  have hdescent : baseEnd_3082076 < baseStart_3082076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082209 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3082209 : Nat := 118140960795 + 3082209 * 2 ^ 59
def prefixEnd_3082209 : Nat := 4983230072969 + 3 ^ 40 * 3082209 * 2
def baseEnd_3082209 : Nat := 1055103129742557717875123

theorem tailTrace_3082209 : CollatzResearch.WordTrace tailWord_3082209 prefixEnd_3082209 1055103129742557717875123 := by
  unfold tailWord_3082209
  simp only [CollatzResearch.WordTrace]
  refine ⟨112417397690690667233513681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74944931793793778155675787 112417397690690667233513681)
  ·
    refine ⟨84313048268018000425135261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112417397690690667233513681 84313048268018000425135261)
    ·
      refine ⟨31617393100506750159425723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84313048268018000425135261 31617393100506750159425723)
      ·
        refine ⟨47426089650760125239138585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31617393100506750159425723 47426089650760125239138585)
        ·
          refine ⟨35569567238070093929353939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47426089650760125239138585 35569567238070093929353939)
          ·
            refine ⟨53354350857105140894030909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35569567238070093929353939 53354350857105140894030909)
            ·
              refine ⟨20007881571414427835261591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53354350857105140894030909 20007881571414427835261591)
              ·
                refine ⟨30011822357121641752892387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20007881571414427835261591 30011822357121641752892387)
                ·
                  refine ⟨45017733535682462629338581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30011822357121641752892387 45017733535682462629338581)
                  ·
                    refine ⟨1055103129742557717875123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45017733535682462629338581 1055103129742557717875123)
                    ·
                      rfl

theorem cell22_3082209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3082209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082209 prefixEnd_3082209 := by exact prefixLift 3082209
  have htrace : WordTrace (prefixWord ++ tailWord_3082209) baseStart_3082209 baseEnd_3082209 := by
    simpa [prefixWord, tailWord_3082209, baseEnd_3082209] using wordTrace_append hprefix tailTrace_3082209
  have hstable : (prefixWord ++ tailWord_3082209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082209).length < 2 ^ (prefixWord ++ tailWord_3082209).sum := by decide
  have hdescent : baseEnd_3082209 < baseStart_3082209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082211 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 5]
def baseStart_3082211 : Nat := 118140960795 + 3082211 * 2 ^ 59
def prefixEnd_3082211 : Nat := 4983230072969 + 3 ^ 40 * 3082211 * 2
def baseEnd_3082211 : Nat := 351701271461143459775039

theorem tailTrace_3082211 : CollatzResearch.WordTrace tailWord_3082211 prefixEnd_3082211 351701271461143459775039 := by
  unfold tailWord_3082211
  simp only [CollatzResearch.WordTrace]
  refine ⟨112417470636683421575086487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74944980424455614383390991 112417470636683421575086487)
  ·
    refine ⟨168626205955025132362629731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112417470636683421575086487 168626205955025132362629731)
    ·
      refine ⟨252939308932537698543944597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168626205955025132362629731 252939308932537698543944597)
      ·
        refine ⟨11856530106212704619247403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 252939308932537698543944597 11856530106212704619247403)
        ·
          refine ⟨17784795159319056928871105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856530106212704619247403 17784795159319056928871105)
          ·
            refine ⟨13338596369489292696653329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17784795159319056928871105 13338596369489292696653329)
            ·
              refine ⟨10003947277116969522489997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13338596369489292696653329 10003947277116969522489997)
              ·
                refine ⟨3751480228918863570933749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10003947277116969522489997 3751480228918863570933749)
                ·
                  refine ⟨351701271461143459775039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751480228918863570933749 351701271461143459775039)
                  ·
                    rfl

theorem cell22_3082211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 5].length) (baseStart_3082211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082211 prefixEnd_3082211 := by exact prefixLift 3082211
  have htrace : WordTrace (prefixWord ++ tailWord_3082211) baseStart_3082211 baseEnd_3082211 := by
    simpa [prefixWord, tailWord_3082211, baseEnd_3082211] using wordTrace_append hprefix tailTrace_3082211
  have hstable : (prefixWord ++ tailWord_3082211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082211).length < 2 ^ (prefixWord ++ tailWord_3082211).sum := by decide
  have hdescent : baseEnd_3082211 < baseStart_3082211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082290 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3082290 : Nat := 118140960795 + 3082290 * 2 ^ 59
def prefixEnd_3082290 : Nat := 4983230072969 + 3 ^ 40 * 3082290 * 2
def baseEnd_3082290 : Nat := 351710285899300168866625

theorem tailTrace_3082290 : CollatzResearch.WordTrace tailWord_3082290 prefixEnd_3082290 351710285899300168866625 := by
  unfold tailWord_3082290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28105088000849304516803081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74946901335598145378141549 28105088000849304516803081)
  ·
    refine ⟨21078816000636978387602311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28105088000849304516803081 21078816000636978387602311)
    ·
      refine ⟨31618224000955467581403467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21078816000636978387602311 31618224000955467581403467)
      ·
        refine ⟨47427336001433201372105201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31618224000955467581403467 47427336001433201372105201)
        ·
          refine ⟨35570502001074901029078901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47427336001433201372105201 35570502001074901029078901)
          ·
            refine ⟨3334734562600771971476147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35570502001074901029078901 3334734562600771971476147)
            ·
              refine ⟨5002101843901157957214221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334734562600771971476147 5002101843901157957214221)
              ·
                refine ⟨1875788191462934233955333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5002101843901157957214221 1875788191462934233955333)
                ·
                  refine ⟨351710285899300168866625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875788191462934233955333 351710285899300168866625)
                  ·
                    rfl

theorem cell22_3082290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3082290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082290 prefixEnd_3082290 := by exact prefixLift 3082290
  have htrace : WordTrace (prefixWord ++ tailWord_3082290) baseStart_3082290 baseEnd_3082290 := by
    simpa [prefixWord, tailWord_3082290, baseEnd_3082290] using wordTrace_append hprefix tailTrace_3082290
  have hstable : (prefixWord ++ tailWord_3082290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082290).length < 2 ^ (prefixWord ++ tailWord_3082290).sum := by decide
  have hdescent : baseEnd_3082290 < baseStart_3082290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_3082299 : Nat := 118140960795 + 3082299 * 2 ^ 59
def prefixEnd_3082299 : Nat := 4983230072969 + 3 ^ 40 * 3082299 * 2
def baseEnd_3082299 : Nat := 1055133938581827483124847

theorem tailTrace_3082299 : CollatzResearch.WordTrace tailWord_3082299 prefixEnd_3082299 1055133938581827483124847 := by
  unfold tailWord_3082299
  simp only [CollatzResearch.WordTrace]
  refine ⟨112420680260364612604289951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74947120173576408402859967 112420680260364612604289951)
  ·
    refine ⟨168631020390546918906434927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112420680260364612604289951 168631020390546918906434927)
    ·
      refine ⟨252946530585820378359652391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168631020390546918906434927 252946530585820378359652391)
      ·
        refine ⟨379419795878730567539478587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252946530585820378359652391 379419795878730567539478587)
        ·
          refine ⟨569129693818095851309217881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379419795878730567539478587 569129693818095851309217881)
          ·
            refine ⟨426847270363571888481913411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569129693818095851309217881 426847270363571888481913411)
            ·
              refine ⟨640270905545357832722870117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426847270363571888481913411 640270905545357832722870117)
              ·
                refine ⟨120050794789754593635538147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640270905545357832722870117 120050794789754593635538147)
                ·
                  refine ⟨180076192184631890453307221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120050794789754593635538147 180076192184631890453307221)
                  ·
                    refine ⟨1055133938581827483124847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180076192184631890453307221 1055133938581827483124847)
                    ·
                      rfl

theorem cell22_3082299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_3082299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082299 prefixEnd_3082299 := by exact prefixLift 3082299
  have htrace : WordTrace (prefixWord ++ tailWord_3082299) baseStart_3082299 baseEnd_3082299 := by
    simpa [prefixWord, tailWord_3082299, baseEnd_3082299] using wordTrace_append hprefix tailTrace_3082299
  have hstable : (prefixWord ++ tailWord_3082299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082299).length < 2 ^ (prefixWord ++ tailWord_3082299).sum := by decide
  have hdescent : baseEnd_3082299 < baseStart_3082299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082378 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_3082378 : Nat := 118140960795 + 3082378 * 2 ^ 59
def prefixEnd_3082378 : Nat := 4983230072969 + 3 ^ 40 * 3082378 * 2
def baseEnd_3082378 : Nat := 1055160981896297610399605

theorem tailTrace_3082378 : CollatzResearch.WordTrace tailWord_3082378 prefixEnd_3082378 1055160981896297610399605 := by
  unfold tailWord_3082378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28105890406769602274103947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74949041084718939397610525 28105890406769602274103947)
  ·
    refine ⟨42158835610154403411155921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28105890406769602274103947 42158835610154403411155921)
    ·
      refine ⟨31619126707615802558366941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42158835610154403411155921 31619126707615802558366941)
      ·
        refine ⟨11857172515355925959387603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31619126707615802558366941 11857172515355925959387603)
        ·
          refine ⟨17785758773033888939081405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11857172515355925959387603 17785758773033888939081405)
          ·
            refine ⟨6669659539887708352155527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17785758773033888939081405 6669659539887708352155527)
            ·
              refine ⟨10004489309831562528233291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669659539887708352155527 10004489309831562528233291)
              ·
                refine ⟨15006733964747343792349937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004489309831562528233291 15006733964747343792349937)
                ·
                  refine ⟨11255050473560507844262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15006733964747343792349937 11255050473560507844262453)
                  ·
                    refine ⟨1055160981896297610399605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11255050473560507844262453 1055160981896297610399605)
                    ·
                      rfl

theorem cell22_3082378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_3082378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082378 prefixEnd_3082378 := by exact prefixLift 3082378
  have htrace : WordTrace (prefixWord ++ tailWord_3082378) baseStart_3082378 baseEnd_3082378 := by
    simpa [prefixWord, tailWord_3082378, baseEnd_3082378] using wordTrace_append hprefix tailTrace_3082378
  have hstable : (prefixWord ++ tailWord_3082378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082378).length < 2 ^ (prefixWord ++ tailWord_3082378).sum := by decide
  have hdescent : baseEnd_3082378 < baseStart_3082378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082414 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3082414 : Nat := 118140960795 + 3082414 * 2 ^ 59
def prefixEnd_3082414 : Nat := 4983230072969 + 3 ^ 40 * 3082414 * 2
def baseEnd_3082414 : Nat := 351724435144001838833165

theorem tailTrace_3082414 : CollatzResearch.WordTrace tailWord_3082414 prefixEnd_3082414 351724435144001838833165 := by
  unfold tailWord_3082414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053109331868498405590787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74949916436631991496484197 14053109331868498405590787)
  ·
    refine ⟨21079663997802747608386181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14053109331868498405590787 21079663997802747608386181)
    ·
      refine ⟨3952436999588015176572409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21079663997802747608386181 3952436999588015176572409)
      ·
        refine ⟨2964327749691011382429307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3952436999588015176572409 2964327749691011382429307)
        ·
          refine ⟨4446491624536517073643961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964327749691011382429307 4446491624536517073643961)
          ·
            refine ⟨3334868718402387805232971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4446491624536517073643961 3334868718402387805232971)
            ·
              refine ⟨5002303077603581707849457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334868718402387805232971 5002303077603581707849457)
              ·
                refine ⟨3751727308202686280887093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5002303077603581707849457 3751727308202686280887093)
                ·
                  refine ⟨351724435144001838833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751727308202686280887093 351724435144001838833165)
                  ·
                    rfl

theorem cell22_3082414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3082414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082414 prefixEnd_3082414 := by exact prefixLift 3082414
  have htrace : WordTrace (prefixWord ++ tailWord_3082414) baseStart_3082414 baseEnd_3082414 := by
    simpa [prefixWord, tailWord_3082414, baseEnd_3082414] using wordTrace_append hprefix tailTrace_3082414
  have hstable : (prefixWord ++ tailWord_3082414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082414).length < 2 ^ (prefixWord ++ tailWord_3082414).sum := by decide
  have hdescent : baseEnd_3082414 < baseStart_3082414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082577 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 4]
def baseStart_3082577 : Nat := 118140960795 + 3082577 * 2 ^ 59
def prefixEnd_3082577 : Nat := 4983230072969 + 3 ^ 40 * 3082577 * 2
def baseEnd_3082577 : Nat := 351743034554375808224665

theorem tailTrace_3082577 : CollatzResearch.WordTrace tailWord_3082577 prefixEnd_3082577 351743034554375808224665 := by
  unfold tailWord_3082577
  simp only [CollatzResearch.WordTrace]
  refine ⟨112430819753357466082909985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74953879835571644055273323 112430819753357466082909985)
  ·
    refine ⟨84323114815018099562182489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112430819753357466082909985 84323114815018099562182489)
    ·
      refine ⟨63242336111263574671636867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84323114815018099562182489 63242336111263574671636867)
      ·
        refine ⟨94863504166895362007455301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63242336111263574671636867 94863504166895362007455301)
        ·
          refine ⟨17786907031292880376397869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94863504166895362007455301 17786907031292880376397869)
          ·
            refine ⟨6670090136734830141149201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17786907031292880376397869 6670090136734830141149201)
            ·
              refine ⟨5002567602551122605861901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6670090136734830141149201 5002567602551122605861901)
              ·
                refine ⟨1875962850956670977198213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5002567602551122605861901 1875962850956670977198213)
                ·
                  refine ⟨351743034554375808224665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875962850956670977198213 351743034554375808224665)
                  ·
                    rfl

theorem cell22_3082577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_3082577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082577 prefixEnd_3082577 := by exact prefixLift 3082577
  have htrace : WordTrace (prefixWord ++ tailWord_3082577) baseStart_3082577 baseEnd_3082577 := by
    simpa [prefixWord, tailWord_3082577, baseEnd_3082577] using wordTrace_append hprefix tailTrace_3082577
  have hstable : (prefixWord ++ tailWord_3082577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082577).length < 2 ^ (prefixWord ++ tailWord_3082577).sum := by decide
  have hdescent : baseEnd_3082577 < baseStart_3082577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082592 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_3082592 : Nat := 118140960795 + 3082592 * 2 ^ 59
def prefixEnd_3082592 : Nat := 4983230072969 + 3 ^ 40 * 3082592 * 2
def baseEnd_3082592 : Nat := 1055234238469672385548949

theorem tailTrace_3082592 : CollatzResearch.WordTrace tailWord_3082592 prefixEnd_3082592 1055234238469672385548949 := by
  unfold tailWord_3082592
  simp only [CollatzResearch.WordTrace]
  refine ⟨56215683424151561822353015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74954244565535415763137353 56215683424151561822353015)
  ·
    refine ⟨84323525136227342733529523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56215683424151561822353015 84323525136227342733529523)
    ·
      refine ⟨126485287704341014100294285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84323525136227342733529523 126485287704341014100294285)
      ·
        refine ⟨47431982889127880287610357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126485287704341014100294285 47431982889127880287610357)
        ·
          refine ⟨4446748395855738776963471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47431982889127880287610357 4446748395855738776963471)
          ·
            refine ⟨6670122593783608165445207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446748395855738776963471 6670122593783608165445207)
            ·
              refine ⟨10005183890675412248167811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6670122593783608165445207 10005183890675412248167811)
              ·
                refine ⟨15007775836013118372251717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10005183890675412248167811 15007775836013118372251717)
                ·
                  refine ⟨2813957969252459694797197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15007775836013118372251717 2813957969252459694797197)
                  ·
                    refine ⟨1055234238469672385548949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813957969252459694797197 1055234238469672385548949)
                    ·
                      rfl

theorem cell22_3082592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_3082592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082592 prefixEnd_3082592 := by exact prefixLift 3082592
  have htrace : WordTrace (prefixWord ++ tailWord_3082592) baseStart_3082592 baseEnd_3082592 := by
    simpa [prefixWord, tailWord_3082592, baseEnd_3082592] using wordTrace_append hprefix tailTrace_3082592
  have hstable : (prefixWord ++ tailWord_3082592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082592).length < 2 ^ (prefixWord ++ tailWord_3082592).sum := by decide
  have hdescent : baseEnd_3082592 < baseStart_3082592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082620 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_3082620 : Nat := 118140960795 + 3082620 * 2 ^ 59
def prefixEnd_3082620 : Nat := 4983230072969 + 3 ^ 40 * 3082620 * 2
def baseEnd_3082620 : Nat := 1055243823441889645848863

theorem tailTrace_3082620 : CollatzResearch.WordTrace tailWord_3082620 prefixEnd_3082620 1055243823441889645848863 := by
  unfold tailWord_3082620
  simp only [CollatzResearch.WordTrace]
  refine ⟨56216194046100842213362657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74954925394801122951150209 56216194046100842213362657)
  ·
    refine ⟨42162145534575631660021993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56216194046100842213362657 42162145534575631660021993)
    ·
      refine ⟨31621609150931723745016495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42162145534575631660021993 31621609150931723745016495)
      ·
        refine ⟨47432413726397585617524743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31621609150931723745016495 47432413726397585617524743)
        ·
          refine ⟨71148620589596378426287115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47432413726397585617524743 71148620589596378426287115)
          ·
            refine ⟨106722930884394567639430673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71148620589596378426287115 106722930884394567639430673)
            ·
              refine ⟨80042198163295925729573005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106722930884394567639430673 80042198163295925729573005)
              ·
                refine ⟨30015824311235972148589877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80042198163295925729573005 30015824311235972148589877)
                ·
                  refine ⟨2813983529178372388930301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30015824311235972148589877 2813983529178372388930301)
                  ·
                    refine ⟨1055243823441889645848863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813983529178372388930301 1055243823441889645848863)
                    ·
                      rfl

theorem cell22_3082620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_3082620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082620 prefixEnd_3082620 := by exact prefixLift 3082620
  have htrace : WordTrace (prefixWord ++ tailWord_3082620) baseStart_3082620 baseEnd_3082620 := by
    simpa [prefixWord, tailWord_3082620, baseEnd_3082620] using wordTrace_append hprefix tailTrace_3082620
  have hstable : (prefixWord ++ tailWord_3082620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082620).length < 2 ^ (prefixWord ++ tailWord_3082620).sum := by decide
  have hdescent : baseEnd_3082620 < baseStart_3082620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082650 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_3082650 : Nat := 118140960795 + 3082650 * 2 ^ 59
def prefixEnd_3082650 : Nat := 4983230072969 + 3 ^ 40 * 3082650 * 2
def baseEnd_3082650 : Nat := 351751364351659855866257

theorem tailTrace_3082650 : CollatzResearch.WordTrace tailWord_3082650 prefixEnd_3082650 351751364351659855866257 := by
  unfold tailWord_3082650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28108370570523249887579351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74955654854728666366878269 28108370570523249887579351)
  ·
    refine ⟨42162555855784874831369027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28108370570523249887579351 42162555855784874831369027)
    ·
      refine ⟨63243833783677312247053541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42162555855784874831369027 63243833783677312247053541)
      ·
        refine ⟨11858218834439496046322539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63243833783677312247053541 11858218834439496046322539)
        ·
          refine ⟨17787328251659244069483809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11858218834439496046322539 17787328251659244069483809)
          ·
            refine ⟨13340496188744433052112857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17787328251659244069483809 13340496188744433052112857)
            ·
              refine ⟨10005372141558324789084643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13340496188744433052112857 10005372141558324789084643)
              ·
                refine ⟨15008058212337487183626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10005372141558324789084643 15008058212337487183626965)
                ·
                  refine ⟨351751364351659855866257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15008058212337487183626965 351751364351659855866257)
                  ·
                    rfl

theorem cell22_3082650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_3082650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082650 prefixEnd_3082650 := by exact prefixLift 3082650
  have htrace : WordTrace (prefixWord ++ tailWord_3082650) baseStart_3082650 baseEnd_3082650 := by
    simpa [prefixWord, tailWord_3082650, baseEnd_3082650] using wordTrace_append hprefix tailTrace_3082650
  have hstable : (prefixWord ++ tailWord_3082650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082650).length < 2 ^ (prefixWord ++ tailWord_3082650).sum := by decide
  have hdescent : baseEnd_3082650 < baseStart_3082650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082727 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3082727 : Nat := 118140960795 + 3082727 * 2 ^ 59
def prefixEnd_3082727 : Nat := 4983230072969 + 3 ^ 40 * 3082727 * 2
def baseEnd_3082727 : Nat := 1055280451728577033423535

theorem tailTrace_3082727 : CollatzResearch.WordTrace tailWord_3082727 prefixEnd_3082727 1055280451728577033423535 := by
  unfold tailWord_3082727
  simp only [CollatzResearch.WordTrace]
  refine ⟨112436290702814041700870435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74957527135209361133913623 112436290702814041700870435)
  ·
    refine ⟨168654436054221062551305653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112436290702814041700870435 168654436054221062551305653)
    ·
      refine ⟨15811353380083224614184905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168654436054221062551305653 15811353380083224614184905)
      ·
        refine ⟨11858515035062418460638679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15811353380083224614184905 11858515035062418460638679)
        ·
          refine ⟨17787772552593627690958019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11858515035062418460638679 17787772552593627690958019)
          ·
            refine ⟨26681658828890441536437029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17787772552593627690958019 26681658828890441536437029)
            ·
              refine ⟨5002811030416957788081943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26681658828890441536437029 5002811030416957788081943)
              ·
                refine ⟨7504216545625436682122915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002811030416957788081943 7504216545625436682122915)
                ·
                  refine ⟨11256324818438155023184373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504216545625436682122915 11256324818438155023184373)
                  ·
                    refine ⟨1055280451728577033423535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11256324818438155023184373 1055280451728577033423535)
                    ·
                      rfl

theorem cell22_3082727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3082727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082727 prefixEnd_3082727 := by exact prefixLift 3082727
  have htrace : WordTrace (prefixWord ++ tailWord_3082727) baseStart_3082727 baseEnd_3082727 := by
    simpa [prefixWord, tailWord_3082727, baseEnd_3082727] using wordTrace_append hprefix tailTrace_3082727
  have hstable : (prefixWord ++ tailWord_3082727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082727).length < 2 ^ (prefixWord ++ tailWord_3082727).sum := by decide
  have hdescent : baseEnd_3082727 < baseStart_3082727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082742 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3082742 : Nat := 118140960795 + 3082742 * 2 ^ 59
def prefixEnd_3082742 : Nat := 4983230072969 + 3 ^ 40 * 3082742 * 2
def baseEnd_3082742 : Nat := 1055285586535121994298489

theorem tailTrace_3082742 : CollatzResearch.WordTrace tailWord_3082742 prefixEnd_3082742 1055285586535121994298489 := by
  unfold tailWord_3082742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7027302362359981203916655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74957891865173132841777653 7027302362359981203916655)
  ·
    refine ⟨10540953543539971805874983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7027302362359981203916655 10540953543539971805874983)
    ·
      refine ⟨15811430315309957708812475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10540953543539971805874983 15811430315309957708812475)
      ·
        refine ⟨23717145472964936563218713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15811430315309957708812475 23717145472964936563218713)
        ·
          refine ⟨17787859104723702422414035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23717145472964936563218713 17787859104723702422414035)
          ·
            refine ⟨26681788657085553633621053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17787859104723702422414035 26681788657085553633621053)
            ·
              refine ⟨10005670746407082612607895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26681788657085553633621053 10005670746407082612607895)
              ·
                refine ⟨15008506119610623918911843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10005670746407082612607895 15008506119610623918911843)
                ·
                  refine ⟨22512759179415935878367765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15008506119610623918911843 22512759179415935878367765)
                  ·
                    refine ⟨1055285586535121994298489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22512759179415935878367765 1055285586535121994298489)
                    ·
                      rfl

theorem cell22_3082742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3082742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082742 prefixEnd_3082742 := by exact prefixLift 3082742
  have htrace : WordTrace (prefixWord ++ tailWord_3082742) baseStart_3082742 baseEnd_3082742 := by
    simpa [prefixWord, tailWord_3082742, baseEnd_3082742] using wordTrace_append hprefix tailTrace_3082742
  have hstable : (prefixWord ++ tailWord_3082742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082742).length < 2 ^ (prefixWord ++ tailWord_3082742).sum := by decide
  have hdescent : baseEnd_3082742 < baseStart_3082742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082797 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3082797 : Nat := 118140960795 + 3082797 * 2 ^ 59
def prefixEnd_3082797 : Nat := 4983230072969 + 3 ^ 40 * 3082797 * 2
def baseEnd_3082797 : Nat := 351768138053040061391107

theorem tailTrace_3082797 : CollatzResearch.WordTrace tailWord_3082797 prefixEnd_3082797 351768138053040061391107 := by
  unfold tailWord_3082797
  simp only [CollatzResearch.WordTrace]
  refine ⟨112438843812560443655918645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74959229208373629103945763 112438843812560443655918645)
  ·
    refine ⟨10541141607427541592742373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112438843812560443655918645 10541141607427541592742373)
    ·
      refine ⟨1976464051392664048639195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10541141607427541592742373 1976464051392664048639195)
      ·
        refine ⟨2964696077088996072958793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976464051392664048639195 2964696077088996072958793)
        ·
          refine ⟨2223522057816747054719095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2964696077088996072958793 2223522057816747054719095)
          ·
            refine ⟨3335283086725120582078643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223522057816747054719095 3335283086725120582078643)
            ·
              refine ⟨5002924630087680873117965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335283086725120582078643 5002924630087680873117965)
              ·
                refine ⟨1876096736282880327419237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5002924630087680873117965 1876096736282880327419237)
                ·
                  refine ⟨351768138053040061391107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876096736282880327419237 351768138053040061391107)
                  ·
                    rfl

theorem cell22_3082797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3082797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082797 prefixEnd_3082797 := by exact prefixLift 3082797
  have htrace : WordTrace (prefixWord ++ tailWord_3082797) baseStart_3082797 baseEnd_3082797 := by
    simpa [prefixWord, tailWord_3082797, baseEnd_3082797] using wordTrace_append hprefix tailTrace_3082797
  have hstable : (prefixWord ++ tailWord_3082797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082797).length < 2 ^ (prefixWord ++ tailWord_3082797).sum := by decide
  have hdescent : baseEnd_3082797 < baseStart_3082797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082800 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_3082800 : Nat := 118140960795 + 3082800 * 2 ^ 59
def prefixEnd_3082800 : Nat := 4983230072969 + 3 ^ 40 * 3082800 * 2
def baseEnd_3082800 : Nat := 1055305441120429176348311

theorem tailTrace_3082800 : CollatzResearch.WordTrace tailWord_3082800 prefixEnd_3082800 1055305441120429176348311 := by
  unfold tailWord_3082800
  simp only [CollatzResearch.WordTrace]
  refine ⟨56219476615774787584138927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74959302154366383445518569 56219476615774787584138927)
  ·
    refine ⟨84329214923662181376208391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56219476615774787584138927 84329214923662181376208391)
    ·
      refine ⟨126493822385493272064312587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84329214923662181376208391 126493822385493272064312587)
      ·
        refine ⟨189740733578239908096468881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126493822385493272064312587 189740733578239908096468881)
        ·
          refine ⟨142305550183679931072351661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189740733578239908096468881 142305550183679931072351661)
          ·
            refine ⟨53364581318879974152131873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142305550183679931072351661 53364581318879974152131873)
            ·
              refine ⟨40023435989159980614098905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53364581318879974152131873 40023435989159980614098905)
              ·
                refine ⟨30017576991869985460574179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40023435989159980614098905 30017576991869985460574179)
                ·
                  refine ⟨45026365487804978190861269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30017576991869985460574179 45026365487804978190861269)
                  ·
                    refine ⟨1055305441120429176348311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45026365487804978190861269 1055305441120429176348311)
                    ·
                      rfl

theorem cell22_3082800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_3082800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082800 prefixEnd_3082800 := by exact prefixLift 3082800
  have htrace : WordTrace (prefixWord ++ tailWord_3082800) baseStart_3082800 baseEnd_3082800 := by
    simpa [prefixWord, tailWord_3082800, baseEnd_3082800] using wordTrace_append hprefix tailTrace_3082800
  have hstable : (prefixWord ++ tailWord_3082800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082800).length < 2 ^ (prefixWord ++ tailWord_3082800).sum := by decide
  have hdescent : baseEnd_3082800 < baseStart_3082800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082823 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3082823 : Nat := 118140960795 + 3082823 * 2 ^ 59
def prefixEnd_3082823 : Nat := 4983230072969 + 3 ^ 40 * 3082823 * 2
def baseEnd_3082823 : Nat := 1055313314490464783023241

theorem tailTrace_3082823 : CollatzResearch.WordTrace tailWord_3082823 prefixEnd_3082823 1055313314490464783023241 := by
  unfold tailWord_3082823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112439792110466250096365123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74959861406977500064243415 112439792110466250096365123)
  ·
    refine ⟨168659688165699375144547685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112439792110466250096365123 168659688165699375144547685)
    ·
      refine ⟨31623691531068632839602691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168659688165699375144547685 31623691531068632839602691)
      ·
        refine ⟨47435537296602949259404037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31623691531068632839602691 47435537296602949259404037)
        ·
          refine ⟨8894163243113052986138257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47435537296602949259404037 8894163243113052986138257)
          ·
            refine ⟨6670622432334789739603693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8894163243113052986138257 6670622432334789739603693)
            ·
              refine ⟨2501483412125546152351385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6670622432334789739603693 2501483412125546152351385)
              ·
                refine ⟨1876112559094159614263539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2501483412125546152351385 1876112559094159614263539)
                ·
                  refine ⟨2814168838641239421395309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876112559094159614263539 2814168838641239421395309)
                  ·
                    refine ⟨1055313314490464783023241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814168838641239421395309 1055313314490464783023241)
                    ·
                      rfl

theorem cell22_3082823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3082823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082823 prefixEnd_3082823 := by exact prefixLift 3082823
  have htrace : WordTrace (prefixWord ++ tailWord_3082823) baseStart_3082823 baseEnd_3082823 := by
    simpa [prefixWord, tailWord_3082823, baseEnd_3082823] using wordTrace_append hprefix tailTrace_3082823
  have hstable : (prefixWord ++ tailWord_3082823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082823).length < 2 ^ (prefixWord ++ tailWord_3082823).sum := by decide
  have hdescent : baseEnd_3082823 < baseStart_3082823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082836 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3082836 : Nat := 118140960795 + 3082836 * 2 ^ 59
def prefixEnd_3082836 : Nat := 4983230072969 + 3 ^ 40 * 3082836 * 2
def baseEnd_3082836 : Nat := 351772588218712360816067

theorem tailTrace_3082836 : CollatzResearch.WordTrace tailWord_3082836 prefixEnd_3082836 351772588218712360816067 := by
  unfold tailWord_3082836
  simp only [CollatzResearch.WordTrace]
  refine ⟨56220133129709576658294181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74960177506279435544392241 56220133129709576658294181)
  ·
    refine ⟨10541274961820545623430159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56220133129709576658294181 10541274961820545623430159)
    ·
      refine ⟨15811912442730818435145239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10541274961820545623430159 15811912442730818435145239)
      ·
        refine ⟨23717868664096227652717859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15811912442730818435145239 23717868664096227652717859)
        ·
          refine ⟨35576802996144341479076789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23717868664096227652717859 35576802996144341479076789)
          ·
            refine ⟨3335325280888532013663449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35576802996144341479076789 3335325280888532013663449)
            ·
              refine ⟨2501493960666399010247587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335325280888532013663449 2501493960666399010247587)
              ·
                refine ⟨3752240940999598515371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501493960666399010247587 3752240940999598515371381)
                ·
                  refine ⟨351772588218712360816067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752240940999598515371381 351772588218712360816067)
                  ·
                    rfl

theorem cell22_3082836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3082836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082836 prefixEnd_3082836 := by exact prefixLift 3082836
  have htrace : WordTrace (prefixWord ++ tailWord_3082836) baseStart_3082836 baseEnd_3082836 := by
    simpa [prefixWord, tailWord_3082836, baseEnd_3082836] using wordTrace_append hprefix tailTrace_3082836
  have hstable : (prefixWord ++ tailWord_3082836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082836).length < 2 ^ (prefixWord ++ tailWord_3082836).sum := by decide
  have hdescent : baseEnd_3082836 < baseStart_3082836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082849 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3082849 : Nat := 118140960795 + 3082849 * 2 ^ 59
def prefixEnd_3082849 : Nat := 4983230072969 + 3 ^ 40 * 3082849 * 2
def baseEnd_3082849 : Nat := 1055322214821809381873161

theorem tailTrace_3082849 : CollatzResearch.WordTrace tailWord_3082849 prefixEnd_3082849 1055322214821809381873161 := by
  unfold tailWord_3082849
  simp only [CollatzResearch.WordTrace]
  refine ⟨112440740408372056536811601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74960493605581371024541067 112440740408372056536811601)
  ·
    refine ⟨84330555306279042402608701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112440740408372056536811601 84330555306279042402608701)
    ·
      refine ⟨31623958239854640900978263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84330555306279042402608701 31623958239854640900978263)
      ·
        refine ⟨47435937359781961351467395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31623958239854640900978263 47435937359781961351467395)
        ·
          refine ⟨71153906039672942027201093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47435937359781961351467395 71153906039672942027201093)
          ·
            refine ⟨13341357382438676630100205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71153906039672942027201093 13341357382438676630100205)
            ·
              refine ⟨5003009018414503736287577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13341357382438676630100205 5003009018414503736287577)
              ·
                refine ⟨3752256763810877802215683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003009018414503736287577 3752256763810877802215683)
                ·
                  refine ⟨5628385145716316703323525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752256763810877802215683 5628385145716316703323525)
                  ·
                    refine ⟨1055322214821809381873161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628385145716316703323525 1055322214821809381873161)
                    ·
                      rfl

theorem cell22_3082849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3082849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082849 prefixEnd_3082849 := by exact prefixLift 3082849
  have htrace : WordTrace (prefixWord ++ tailWord_3082849) baseStart_3082849 baseEnd_3082849 := by
    simpa [prefixWord, tailWord_3082849, baseEnd_3082849] using wordTrace_append hprefix tailTrace_3082849
  have hstable : (prefixWord ++ tailWord_3082849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082849).length < 2 ^ (prefixWord ++ tailWord_3082849).sum := by decide
  have hdescent : baseEnd_3082849 < baseStart_3082849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082941 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_3082941 : Nat := 118140960795 + 3082941 * 2 ^ 59
def prefixEnd_3082941 : Nat := 4983230072969 + 3 ^ 40 * 3082941 * 2
def baseEnd_3082941 : Nat := 1055353708301951808572879

theorem tailTrace_3082941 : CollatzResearch.WordTrace tailWord_3082941 prefixEnd_3082941 1055353708301951808572879 := by
  unfold tailWord_3082941
  simp only [CollatzResearch.WordTrace]
  refine ⟨112444095924038756249160677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74962730616025837499440451 112444095924038756249160677)
  ·
    refine ⟨21083267985757266796717627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112444095924038756249160677 21083267985757266796717627)
    ·
      refine ⟨31624901978635900195076441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21083267985757266796717627 31624901978635900195076441)
      ·
        refine ⟨23718676483976925146307331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31624901978635900195076441 23718676483976925146307331)
        ·
          refine ⟨35578014725965387719460997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23718676483976925146307331 35578014725965387719460997)
          ·
            refine ⟨6670877761118510197398937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35578014725965387719460997 6670877761118510197398937)
            ·
              refine ⟨5003158320838882648049203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6670877761118510197398937 5003158320838882648049203)
              ·
                refine ⟨7504737481258323972073805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003158320838882648049203 7504737481258323972073805)
                ·
                  refine ⟨2814276555471871489527677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7504737481258323972073805 2814276555471871489527677)
                  ·
                    refine ⟨1055353708301951808572879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814276555471871489527677 1055353708301951808572879)
                    ·
                      rfl

theorem cell22_3082941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_3082941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3082941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3082941 prefixEnd_3082941 := by exact prefixLift 3082941
  have htrace : WordTrace (prefixWord ++ tailWord_3082941) baseStart_3082941 baseEnd_3082941 := by
    simpa [prefixWord, tailWord_3082941, baseEnd_3082941] using wordTrace_append hprefix tailTrace_3082941
  have hstable : (prefixWord ++ tailWord_3082941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082941).length < 2 ^ (prefixWord ++ tailWord_3082941).sum := by decide
  have hdescent : baseEnd_3082941 < baseStart_3082941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083027 : List Nat := [1, 1, 1, 2, 1, 3, 3, 10]
def baseStart_3083027 : Nat := 118140960795 + 3083027 * 2 ^ 59
def prefixEnd_3083027 : Nat := 4983230072969 + 3 ^ 40 * 3083027 * 2
def baseEnd_3083027 : Nat := 117264794206608472324735

theorem tailTrace_3083027 : CollatzResearch.WordTrace tailWord_3083027 prefixEnd_3083027 117264794206608472324735 := by
  unfold tailWord_3083027
  simp only [CollatzResearch.WordTrace]
  refine ⟨112447232601727192936791335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74964821734484795291194223 112447232601727192936791335)
  ·
    refine ⟨168670848902590789405187003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112447232601727192936791335 168670848902590789405187003)
    ·
      refine ⟨253006273353886184107780505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168670848902590789405187003 253006273353886184107780505)
      ·
        refine ⟨189754705015414638080835379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253006273353886184107780505 189754705015414638080835379)
        ·
          refine ⟨284632057523121957121253069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189754705015414638080835379 284632057523121957121253069)
          ·
            refine ⟨106737021571170733920469901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284632057523121957121253069 106737021571170733920469901)
            ·
              refine ⟨40026383089189025220176213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106737021571170733920469901 40026383089189025220176213)
              ·
                refine ⟨117264794206608472324735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40026383089189025220176213 117264794206608472324735)
                ·
                  rfl

theorem cell22_3083027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 10].length) (baseStart_3083027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083027 prefixEnd_3083027 := by exact prefixLift 3083027
  have htrace : WordTrace (prefixWord ++ tailWord_3083027) baseStart_3083027 baseEnd_3083027 := by
    simpa [prefixWord, tailWord_3083027, baseEnd_3083027] using wordTrace_append hprefix tailTrace_3083027
  have hstable : (prefixWord ++ tailWord_3083027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083027).length < 2 ^ (prefixWord ++ tailWord_3083027).sum := by decide
  have hdescent : baseEnd_3083027 < baseStart_3083027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083031 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3083031 : Nat := 118140960795 + 3083031 * 2 ^ 59
def prefixEnd_3083031 : Nat := 4983230072969 + 3 ^ 40 * 3083031 * 2
def baseEnd_3083031 : Nat := 1055384517141221573822603

theorem tailTrace_3083031 : CollatzResearch.WordTrace tailWord_3083031 prefixEnd_3083031 1055384517141221573822603 := by
  unfold tailWord_3083031
  simp only [CollatzResearch.WordTrace]
  refine ⟨112447378493712701619936947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74964918995808467746624631 112447378493712701619936947)
  ·
    refine ⟨168671067740569052429905421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112447378493712701619936947 168671067740569052429905421)
    ·
      refine ⟨63251650402713394661214533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168671067740569052429905421 63251650402713394661214533)
      ·
        refine ⟨11859684450508761498977725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63251650402713394661214533 11859684450508761498977725)
        ·
          refine ⟨4447381668940785562116647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11859684450508761498977725 4447381668940785562116647)
          ·
            refine ⟨6671072503411178343174971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4447381668940785562116647 6671072503411178343174971)
            ·
              refine ⟨10006608755116767514762457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671072503411178343174971 10006608755116767514762457)
              ·
                refine ⟨7504956566337575636071843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10006608755116767514762457 7504956566337575636071843)
                ·
                  refine ⟨11257434849506363454107765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504956566337575636071843 11257434849506363454107765)
                  ·
                    refine ⟨1055384517141221573822603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11257434849506363454107765 1055384517141221573822603)
                    ·
                      rfl

theorem cell22_3083031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3083031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083031 prefixEnd_3083031 := by exact prefixLift 3083031
  have htrace : WordTrace (prefixWord ++ tailWord_3083031) baseStart_3083031 baseEnd_3083031 := by
    simpa [prefixWord, tailWord_3083031, baseEnd_3083031] using wordTrace_append hprefix tailTrace_3083031
  have hstable : (prefixWord ++ tailWord_3083031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083031).length < 2 ^ (prefixWord ++ tailWord_3083031).sum := by decide
  have hdescent : baseEnd_3083031 < baseStart_3083031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083044 : List Nat := [2, 3, 1, 3, 3, 10]
def baseStart_3083044 : Nat := 118140960795 + 3083044 * 2 ^ 59
def prefixEnd_3083044 : Nat := 4983230072969 + 3 ^ 40 * 3083044 * 2
def baseEnd_3083044 : Nat := 13029493423541899669723

theorem tailTrace_3083044 : CollatzResearch.WordTrace tailWord_3083044 prefixEnd_3083044 13029493423541899669723 := by
  unfold tailWord_3083044
  simp only [CollatzResearch.WordTrace]
  refine ⟨56223926321332802420080093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74965235095110403226773457 56223926321332802420080093)
  ·
    refine ⟨21083972370499800907530035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56223926321332802420080093 21083972370499800907530035)
    ·
      refine ⟨31625958555749701361295053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21083972370499800907530035 31625958555749701361295053)
      ·
        refine ⟨11859734458406138010485645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31625958555749701361295053 11859734458406138010485645)
        ·
          refine ⟨4447400421902301753932117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11859734458406138010485645 4447400421902301753932117)
          ·
            refine ⟨13029493423541899669723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4447400421902301753932117 13029493423541899669723)
            ·
              rfl

theorem cell22_3083044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 10].length) (baseStart_3083044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083044 prefixEnd_3083044 := by exact prefixLift 3083044
  have htrace : WordTrace (prefixWord ++ tailWord_3083044) baseStart_3083044 baseEnd_3083044 := by
    simpa [prefixWord, tailWord_3083044, baseEnd_3083044] using wordTrace_append hprefix tailTrace_3083044
  have hstable : (prefixWord ++ tailWord_3083044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083044).length < 2 ^ (prefixWord ++ tailWord_3083044).sum := by decide
  have hdescent : baseEnd_3083044 < baseStart_3083044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083048 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3083048 : Nat := 118140960795 + 3083048 * 2 ^ 59
def prefixEnd_3083048 : Nat := 4983230072969 + 3 ^ 40 * 3083048 * 2
def baseEnd_3083048 : Nat := 1055390336588639196147551

theorem tailTrace_3083048 : CollatzResearch.WordTrace tailWord_3083048 prefixEnd_3083048 1055390336588639196147551 := by
  unfold tailWord_3083048
  simp only [CollatzResearch.WordTrace]
  refine ⟨56223999267325556761652899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74965332356434075682203865 56223999267325556761652899)
  ·
    refine ⟨84335998900988335142479349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56223999267325556761652899 84335998900988335142479349)
    ·
      refine ⟨7906499896967656419607439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84335998900988335142479349 7906499896967656419607439)
      ·
        refine ⟨11859749845451484629411159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906499896967656419607439 11859749845451484629411159)
        ·
          refine ⟨17789624768177226944116739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11859749845451484629411159 17789624768177226944116739)
          ·
            refine ⟨26684437152265840416175109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17789624768177226944116739 26684437152265840416175109)
            ·
              refine ⟨5003331966049845078032833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26684437152265840416175109 5003331966049845078032833)
              ·
                refine ⟨3752498974537383808524625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003331966049845078032833 3752498974537383808524625)
                ·
                  refine ⟨2814374230903037856393469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752498974537383808524625 2814374230903037856393469)
                  ·
                    refine ⟨1055390336588639196147551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814374230903037856393469 1055390336588639196147551)
                    ·
                      rfl

theorem cell22_3083048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3083048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083048 prefixEnd_3083048 := by exact prefixLift 3083048
  have htrace : WordTrace (prefixWord ++ tailWord_3083048) baseStart_3083048 baseEnd_3083048 := by
    simpa [prefixWord, tailWord_3083048, baseEnd_3083048] using wordTrace_append hprefix tailTrace_3083048
  have hstable : (prefixWord ++ tailWord_3083048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083048).length < 2 ^ (prefixWord ++ tailWord_3083048).sum := by decide
  have hdescent : baseEnd_3083048 < baseStart_3083048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083050 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_3083050 : Nat := 118140960795 + 3083050 * 2 ^ 59
def prefixEnd_3083050 : Nat := 4983230072969 + 3 ^ 40 * 3083050 * 2
def baseEnd_3083050 : Nat := 351797007076503952532515

theorem tailTrace_3083050 : CollatzResearch.WordTrace tailWord_3083050 prefixEnd_3083050 351797007076503952532515 := by
  unfold tailWord_3083050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112017870160966966219651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74965380987095911909919069 28112017870160966966219651)
  ·
    refine ⟨42168026805241450449329477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28112017870160966966219651 42168026805241450449329477)
    ·
      refine ⟨7906505025982771959249277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42168026805241450449329477 7906505025982771959249277)
      ·
        refine ⟨2964939384743539484718479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7906505025982771959249277 2964939384743539484718479)
        ·
          refine ⟨4447409077115309227077719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964939384743539484718479 4447409077115309227077719)
          ·
            refine ⟨6671113615672963840616579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4447409077115309227077719 6671113615672963840616579)
            ·
              refine ⟨10006670423509445760924869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671113615672963840616579 10006670423509445760924869)
              ·
                refine ⟨1876250704408021080173413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10006670423509445760924869 1876250704408021080173413)
                ·
                  refine ⟨351797007076503952532515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876250704408021080173413 351797007076503952532515)
                  ·
                    rfl

theorem cell22_3083050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_3083050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083050 prefixEnd_3083050 := by exact prefixLift 3083050
  have htrace : WordTrace (prefixWord ++ tailWord_3083050) baseStart_3083050 baseEnd_3083050 := by
    simpa [prefixWord, tailWord_3083050, baseEnd_3083050] using wordTrace_append hprefix tailTrace_3083050
  have hstable : (prefixWord ++ tailWord_3083050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083050).length < 2 ^ (prefixWord ++ tailWord_3083050).sum := by decide
  have hdescent : baseEnd_3083050 < baseStart_3083050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083061 : List Nat := [1, 3, 3, 1, 3, 3, 1, 7]
def baseStart_3083061 : Nat := 118140960795 + 3083061 * 2 ^ 59
def prefixEnd_3083061 : Nat := 4983230072969 + 3 ^ 40 * 3083061 * 2
def baseEnd_3083061 : Nat := 117266087417145721730279

theorem tailTrace_3083061 : CollatzResearch.WordTrace tailWord_3083061 prefixEnd_3083061 117266087417145721730279 := by
  unfold tailWord_3083061
  simp only [CollatzResearch.WordTrace]
  refine ⟨112448472683604016743529037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74965648455736011162352691 112448472683604016743529037)
  ·
    refine ⟨42168177256351506278823389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112448472683604016743529037 42168177256351506278823389)
    ·
      refine ⟨15813066471131814854558771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42168177256351506278823389 15813066471131814854558771)
      ·
        refine ⟨23719599706697722281838157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813066471131814854558771 23719599706697722281838157)
        ·
          refine ⟨8894849890011645855689309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23719599706697722281838157 8894849890011645855689309)
          ·
            refine ⟨3335568708754367195883491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8894849890011645855689309 3335568708754367195883491)
            ·
              refine ⟨5003353063131550793825237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335568708754367195883491 5003353063131550793825237)
              ·
                refine ⟨117266087417145721730279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5003353063131550793825237 117266087417145721730279)
                ·
                  rfl

theorem cell22_3083061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 7].length) (baseStart_3083061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083061 prefixEnd_3083061 := by exact prefixLift 3083061
  have htrace : WordTrace (prefixWord ++ tailWord_3083061) baseStart_3083061 baseEnd_3083061 := by
    simpa [prefixWord, tailWord_3083061, baseEnd_3083061] using wordTrace_append hprefix tailTrace_3083061
  have hstable : (prefixWord ++ tailWord_3083061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083061).length < 2 ^ (prefixWord ++ tailWord_3083061).sum := by decide
  have hdescent : baseEnd_3083061 < baseStart_3083061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083104 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_3083104 : Nat := 118140960795 + 3083104 * 2 ^ 59
def prefixEnd_3083104 : Nat := 4983230072969 + 3 ^ 40 * 3083104 * 2
def baseEnd_3083104 : Nat := 1055409506533073716747379

theorem tailTrace_3083104 : CollatzResearch.WordTrace tailWord_3083104 prefixEnd_3083104 1055409506533073716747379 := by
  unfold tailWord_3083104
  simp only [CollatzResearch.WordTrace]
  refine ⟨56225020511224117543672183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74966694014965490058229577 56225020511224117543672183)
  ·
    refine ⟨84337530766836176315508275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56225020511224117543672183 84337530766836176315508275)
    ·
      refine ⟨126506296150254264473262413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84337530766836176315508275 126506296150254264473262413)
      ·
        refine ⟨47439861056345349177473405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126506296150254264473262413 47439861056345349177473405)
        ·
          refine ⟨17789947896129505941552527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47439861056345349177473405 17789947896129505941552527)
          ·
            refine ⟨26684921844194258912328791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17789947896129505941552527 26684921844194258912328791)
            ·
              refine ⟨40027382766291388368493187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26684921844194258912328791 40027382766291388368493187)
              ·
                refine ⟨60041074149437082552739781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40027382766291388368493187 60041074149437082552739781)
                ·
                  refine ⟨11257701403019452978638709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60041074149437082552739781 11257701403019452978638709)
                  ·
                    refine ⟨1055409506533073716747379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11257701403019452978638709 1055409506533073716747379)
                    ·
                      rfl

theorem cell22_3083104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_3083104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083104 prefixEnd_3083104 := by exact prefixLift 3083104
  have htrace : WordTrace (prefixWord ++ tailWord_3083104) baseStart_3083104 baseEnd_3083104 := by
    simpa [prefixWord, tailWord_3083104, baseEnd_3083104] using wordTrace_append hprefix tailTrace_3083104
  have hstable : (prefixWord ++ tailWord_3083104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083104).length < 2 ^ (prefixWord ++ tailWord_3083104).sum := by decide
  have hdescent : baseEnd_3083104 < baseStart_3083104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083119 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_3083119 : Nat := 118140960795 + 3083119 * 2 ^ 59
def prefixEnd_3083119 : Nat := 4983230072969 + 3 ^ 40 * 3083119 * 2
def baseEnd_3083119 : Nat := 1055414641339618677622333

theorem tailTrace_3083119 : CollatzResearch.WordTrace tailWord_3083119 prefixEnd_3083119 1055414641339618677622333 := by
  unfold tailWord_3083119
  simp only [CollatzResearch.WordTrace]
  refine ⟨112450588117393892649140411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74967058744929261766093607 112450588117393892649140411)
  ·
    refine ⟨168675882176090838973710617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112450588117393892649140411 168675882176090838973710617)
    ·
      refine ⟨126506911632068129230282963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168675882176090838973710617 126506911632068129230282963)
      ·
        refine ⟨189760367448102193845424445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126506911632068129230282963 189760367448102193845424445)
        ·
          refine ⟨71160137793038322692034167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189760367448102193845424445 71160137793038322692034167)
          ·
            refine ⟨106740206689557484038051251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71160137793038322692034167 106740206689557484038051251)
            ·
              refine ⟨160110310034336226057076877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106740206689557484038051251 160110310034336226057076877)
              ·
                refine ⟨60041366262876084771403829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160110310034336226057076877 60041366262876084771403829)
                ·
                  refine ⟨5628878087144632947319109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60041366262876084771403829 5628878087144632947319109)
                  ·
                    refine ⟨1055414641339618677622333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628878087144632947319109 1055414641339618677622333)
                    ·
                      rfl

theorem cell22_3083119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_3083119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083119 prefixEnd_3083119 := by exact prefixLift 3083119
  have htrace : WordTrace (prefixWord ++ tailWord_3083119) baseStart_3083119 baseEnd_3083119 := by
    simpa [prefixWord, tailWord_3083119, baseEnd_3083119] using wordTrace_append hprefix tailTrace_3083119
  have hstable : (prefixWord ++ tailWord_3083119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083119).length < 2 ^ (prefixWord ++ tailWord_3083119).sum := by decide
  have hdescent : baseEnd_3083119 < baseStart_3083119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083198 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3083198 : Nat := 118140960795 + 3083198 * 2 ^ 59
def prefixEnd_3083198 : Nat := 4983230072969 + 3 ^ 40 * 3083198 * 2
def baseEnd_3083198 : Nat := 1055441684654088804897091

theorem tailTrace_3083198 : CollatzResearch.WordTrace tailWord_3083198 prefixEnd_3083198 1055441684654088804897091 := by
  unfold tailWord_3083198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056683685513461142658281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74968979656071792760844165 14056683685513461142658281)
  ·
    refine ⟨10542512764135095856993711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14056683685513461142658281 10542512764135095856993711)
    ·
      refine ⟨15813769146202643785490567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10542512764135095856993711 15813769146202643785490567)
      ·
        refine ⟨23720653719303965678235851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813769146202643785490567 23720653719303965678235851)
        ·
          refine ⟨35580980578955948517353777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23720653719303965678235851 35580980578955948517353777)
          ·
            refine ⟨26685735434216961388015333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35580980578955948517353777 26685735434216961388015333)
            ·
              refine ⟨5003575393915680260252875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26685735434216961388015333 5003575393915680260252875)
              ·
                refine ⟨7505363090873520390379313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003575393915680260252875 7505363090873520390379313)
                ·
                  refine ⟨5629022318155140292784485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505363090873520390379313 5629022318155140292784485)
                  ·
                    refine ⟨1055441684654088804897091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629022318155140292784485 1055441684654088804897091)
                    ·
                      rfl

theorem cell22_3083198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3083198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083198 prefixEnd_3083198 := by exact prefixLift 3083198
  have htrace : WordTrace (prefixWord ++ tailWord_3083198) baseStart_3083198 baseEnd_3083198 := by
    simpa [prefixWord, tailWord_3083198, baseEnd_3083198] using wordTrace_append hprefix tailTrace_3083198
  have hstable : (prefixWord ++ tailWord_3083198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083198).length < 2 ^ (prefixWord ++ tailWord_3083198).sum := by decide
  have hdescent : baseEnd_3083198 < baseStart_3083198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083209 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_3083209 : Nat := 118140960795 + 3083209 * 2 ^ 59
def prefixEnd_3083209 : Nat := 4983230072969 + 3 ^ 40 * 3083209 * 2
def baseEnd_3083209 : Nat := 1055445450178888442872057

theorem tailTrace_3083209 : CollatzResearch.WordTrace tailWord_3083209 prefixEnd_3083209 1055445450178888442872057 := by
  unfold tailWord_3083209
  simp only [CollatzResearch.WordTrace]
  refine ⟨112453870687067838019916681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74969247124711892013277787 112453870687067838019916681)
  ·
    refine ⟨84340403015300878514937511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112453870687067838019916681 84340403015300878514937511)
    ·
      refine ⟨126510604522951317772406267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84340403015300878514937511 126510604522951317772406267)
      ·
        refine ⟨189765906784426976658609401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126510604522951317772406267 189765906784426976658609401)
        ·
          refine ⟨142324430088320232493957051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189765906784426976658609401 142324430088320232493957051)
          ·
            refine ⟨213486645132480348740935577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142324430088320232493957051 213486645132480348740935577)
            ·
              refine ⟨160114983849360261555701683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213486645132480348740935577 160114983849360261555701683)
              ·
                refine ⟨240172475774040392333552525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160114983849360261555701683 240172475774040392333552525)
                ·
                  refine ⟨90064678415265147125082197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240172475774040392333552525 90064678415265147125082197)
                  ·
                    refine ⟨1055445450178888442872057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90064678415265147125082197 1055445450178888442872057)
                    ·
                      rfl

theorem cell22_3083209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_3083209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083209 prefixEnd_3083209 := by exact prefixLift 3083209
  have htrace : WordTrace (prefixWord ++ tailWord_3083209) baseStart_3083209 baseEnd_3083209 := by
    simpa [prefixWord, tailWord_3083209, baseEnd_3083209] using wordTrace_append hprefix tailTrace_3083209
  have hstable : (prefixWord ++ tailWord_3083209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083209).length < 2 ^ (prefixWord ++ tailWord_3083209).sum := by decide
  have hdescent : baseEnd_3083209 < baseStart_3083209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083226 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_3083226 : Nat := 118140960795 + 3083226 * 2 ^ 59
def prefixEnd_3083226 : Nat := 4983230072969 + 3 ^ 40 * 3083226 * 2
def baseEnd_3083226 : Nat := 1055451269626306065197005

theorem tailTrace_3083226 : CollatzResearch.WordTrace tailWord_3083226 prefixEnd_3083226 1055451269626306065197005 := by
  unfold tailWord_3083226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28113622682001562480821383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74969660485337499948857021 28113622682001562480821383)
  ·
    refine ⟨42170434023002343721232075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28113622682001562480821383 42170434023002343721232075)
    ·
      refine ⟨63255651034503515581848113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42170434023002343721232075 63255651034503515581848113)
      ·
        refine ⟨47441738275877636686386085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63255651034503515581848113 47441738275877636686386085)
        ·
          refine ⟨8895325926727056878697391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47441738275877636686386085 8895325926727056878697391)
          ·
            refine ⟨13342988890090585318046087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895325926727056878697391 13342988890090585318046087)
            ·
              refine ⟨20014483335135877977069131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13342988890090585318046087 20014483335135877977069131)
              ·
                refine ⟨30021725002703816965603697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20014483335135877977069131 30021725002703816965603697)
                ·
                  refine ⟨22516293752027862724202773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30021725002703816965603697 22516293752027862724202773)
                  ·
                    refine ⟨1055451269626306065197005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22516293752027862724202773 1055451269626306065197005)
                    ·
                      rfl

theorem cell22_3083226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_3083226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083226 prefixEnd_3083226 := by exact prefixLift 3083226
  have htrace : WordTrace (prefixWord ++ tailWord_3083226) baseStart_3083226 baseEnd_3083226 := by
    simpa [prefixWord, tailWord_3083226, baseEnd_3083226] using wordTrace_append hprefix tailTrace_3083226
  have hstable : (prefixWord ++ tailWord_3083226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083226).length < 2 ^ (prefixWord ++ tailWord_3083226).sum := by decide
  have hdescent : baseEnd_3083226 < baseStart_3083226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083320 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_3083320 : Nat := 118140960795 + 3083320 * 2 ^ 59
def prefixEnd_3083320 : Nat := 4983230072969 + 3 ^ 40 * 3083320 * 2
def baseEnd_3083320 : Nat := 351827815915773717782239

theorem tailTrace_3083320 : CollatzResearch.WordTrace tailWord_3083320 prefixEnd_3083320 351827815915773717782239 := by
  unfold tailWord_3083320
  simp only [CollatzResearch.WordTrace]
  refine ⟨56228959594832851988603707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74971946126443802651471609 56228959594832851988603707)
  ·
    refine ⟨84343439392249277982905561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56228959594832851988603707 84343439392249277982905561)
    ·
      refine ⟨63257579544186958487179171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84343439392249277982905561 63257579544186958487179171)
      ·
        refine ⟨94886369316280437730768757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63257579544186958487179171 94886369316280437730768757)
        ·
          refine ⟨8895597123401291037259571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94886369316280437730768757 8895597123401291037259571)
          ·
            refine ⟨13343395685101936555889357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895597123401291037259571 13343395685101936555889357)
            ·
              refine ⟨5003773381913226208458509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13343395685101936555889357 5003773381913226208458509)
              ·
                refine ⟨1876415018217459828171941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5003773381913226208458509 1876415018217459828171941)
                ·
                  refine ⟨351827815915773717782239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876415018217459828171941 351827815915773717782239)
                  ·
                    rfl

theorem cell22_3083320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_3083320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083320 prefixEnd_3083320 := by exact prefixLift 3083320
  have htrace : WordTrace (prefixWord ++ tailWord_3083320) baseStart_3083320 baseEnd_3083320 := by
    simpa [prefixWord, tailWord_3083320, baseEnd_3083320] using wordTrace_append hprefix tailTrace_3083320
  have hstable : (prefixWord ++ tailWord_3083320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083320).length < 2 ^ (prefixWord ++ tailWord_3083320).sum := by decide
  have hdescent : baseEnd_3083320 < baseStart_3083320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083363 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 5, 3]
def baseStart_3083363 : Nat := 118140960795 + 3083363 * 2 ^ 59
def prefixEnd_3083363 : Nat := 4983230072969 + 3 ^ 40 * 3083363 * 2
def baseEnd_3083363 : Nat := 1055498167526083374521585

theorem tailTrace_3083363 : CollatzResearch.WordTrace tailWord_3083363 prefixEnd_3083363 1055498167526083374521585 := by
  unfold tailWord_3083363
  simp only [CollatzResearch.WordTrace]
  refine ⟨112459487528509922321022743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74972991685673281547348495 112459487528509922321022743)
  ·
    refine ⟨168689231292764883481534115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112459487528509922321022743 168689231292764883481534115)
    ·
      refine ⟨253033846939147325222301173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168689231292764883481534115 253033846939147325222301173)
      ·
        refine ⟨23721923150545061739590735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253033846939147325222301173 23721923150545061739590735)
        ·
          refine ⟨35582884725817592609386103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23721923150545061739590735 35582884725817592609386103)
          ·
            refine ⟨53374327088726388914079155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35582884725817592609386103 53374327088726388914079155)
            ·
              refine ⟨80061490633089583371118733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53374327088726388914079155 80061490633089583371118733)
              ·
                refine ⟨30023058987408593764169525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80061490633089583371118733 30023058987408593764169525)
                ·
                  refine ⟨2814661780069555665390893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30023058987408593764169525 2814661780069555665390893)
                  ·
                    refine ⟨1055498167526083374521585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814661780069555665390893 1055498167526083374521585)
                    ·
                      rfl

theorem cell22_3083363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3].length) (baseStart_3083363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083363 prefixEnd_3083363 := by exact prefixLift 3083363
  have htrace : WordTrace (prefixWord ++ tailWord_3083363) baseStart_3083363 baseEnd_3083363 := by
    simpa [prefixWord, tailWord_3083363, baseEnd_3083363] using wordTrace_append hprefix tailTrace_3083363
  have hstable : (prefixWord ++ tailWord_3083363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083363).length < 2 ^ (prefixWord ++ tailWord_3083363).sum := by decide
  have hdescent : baseEnd_3083363 < baseStart_3083363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083391 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3083391 : Nat := 118140960795 + 3083391 * 2 ^ 59
def prefixEnd_3083391 : Nat := 4983230072969 + 3 ^ 40 * 3083391 * 2
def baseEnd_3083391 : Nat := 1055507752498300634821499

theorem tailTrace_3083391 : CollatzResearch.WordTrace tailWord_3083391 prefixEnd_3083391 1055507752498300634821499 := by
  unfold tailWord_3083391
  simp only [CollatzResearch.WordTrace]
  refine ⟨112460508772408483103042027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74973672514938988735361351 112460508772408483103042027)
  ·
    refine ⟨168690763158612724654563041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112460508772408483103042027 168690763158612724654563041)
    ·
      refine ⟨126518072368959543490922281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168690763158612724654563041 126518072368959543490922281)
      ·
        refine ⟨94888554276719657618191711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126518072368959543490922281 94888554276719657618191711)
        ·
          refine ⟨142332831415079486427287567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94888554276719657618191711 142332831415079486427287567)
          ·
            refine ⟨213499247122619229640931351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142332831415079486427287567 213499247122619229640931351)
            ·
              refine ⟨320248870683928844461397027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213499247122619229640931351 320248870683928844461397027)
              ·
                refine ⟨480373306025893266692095541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320248870683928844461397027 480373306025893266692095541)
                ·
                  refine ⟨45034997439927493752383957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480373306025893266692095541 45034997439927493752383957)
                  ·
                    refine ⟨1055507752498300634821499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45034997439927493752383957 1055507752498300634821499)
                    ·
                      rfl

theorem cell22_3083391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3083391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083391 prefixEnd_3083391 := by exact prefixLift 3083391
  have htrace : WordTrace (prefixWord ++ tailWord_3083391) baseStart_3083391 baseEnd_3083391 := by
    simpa [prefixWord, tailWord_3083391, baseEnd_3083391] using wordTrace_append hprefix tailTrace_3083391
  have hstable : (prefixWord ++ tailWord_3083391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083391).length < 2 ^ (prefixWord ++ tailWord_3083391).sum := by decide
  have hdescent : baseEnd_3083391 < baseStart_3083391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083410 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3083410 : Nat := 118140960795 + 3083410 * 2 ^ 59
def prefixEnd_3083410 : Nat := 4983230072969 + 3 ^ 40 * 3083410 * 2
def baseEnd_3083410 : Nat := 351838085528863639532147

theorem tailTrace_3083410 : CollatzResearch.WordTrace tailWord_3083410 prefixEnd_3083410 351838085528863639532147 := by
  unfold tailWord_3083410
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115300439834912336995921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74974134506226432898655789 28115300439834912336995921)
  ·
    refine ⟨21086475329876184252746941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28115300439834912336995921 21086475329876184252746941)
    ·
      refine ⟨7907428248703569094780103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21086475329876184252746941 7907428248703569094780103)
      ·
        refine ⟨11861142373055353642170155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7907428248703569094780103 11861142373055353642170155)
        ·
          refine ⟨17791713559583030463255233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11861142373055353642170155 17791713559583030463255233)
          ·
            refine ⟨13343785169687272847441425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17791713559583030463255233 13343785169687272847441425)
            ·
              refine ⟨10007838877265454635581069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13343785169687272847441425 10007838877265454635581069)
              ·
                refine ⟨3752939578974545488342901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10007838877265454635581069 3752939578974545488342901)
                ·
                  refine ⟨351838085528863639532147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752939578974545488342901 351838085528863639532147)
                  ·
                    rfl

theorem cell22_3083410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3083410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083410 prefixEnd_3083410 := by exact prefixLift 3083410
  have htrace : WordTrace (prefixWord ++ tailWord_3083410) baseStart_3083410 baseEnd_3083410 := by
    simpa [prefixWord, tailWord_3083410, baseEnd_3083410] using wordTrace_append hprefix tailTrace_3083410
  have hstable : (prefixWord ++ tailWord_3083410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083410).length < 2 ^ (prefixWord ++ tailWord_3083410).sum := by decide
  have hdescent : baseEnd_3083410 < baseStart_3083410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083453 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3083453 : Nat := 118140960795 + 3083453 * 2 ^ 59
def prefixEnd_3083453 : Nat := 4983230072969 + 3 ^ 40 * 3083453 * 2
def baseEnd_3083453 : Nat := 1055528976365353139771309

theorem tailTrace_3083453 : CollatzResearch.WordTrace tailWord_3083453 prefixEnd_3083453 1055528976365353139771309 := by
  unfold tailWord_3083453
  simp only [CollatzResearch.WordTrace]
  refine ⟨112462770098183867691799013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74975180065455911794532675 112462770098183867691799013)
  ·
    refine ⟨21086769393409475192212315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112462770098183867691799013 21086769393409475192212315)
    ·
      refine ⟨31630154090114212788318473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086769393409475192212315 31630154090114212788318473)
      ·
        refine ⟨23722615567585659591238855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31630154090114212788318473 23722615567585659591238855)
        ·
          refine ⟨35583923351378489386858283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23722615567585659591238855 35583923351378489386858283)
          ·
            refine ⟨53375885027067734080287425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35583923351378489386858283 53375885027067734080287425)
            ·
              refine ⟨40031913770300800560215569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53375885027067734080287425 40031913770300800560215569)
              ·
                refine ⟨30023935327725600420161677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40031913770300800560215569 30023935327725600420161677)
                ·
                  refine ⟨11258975747897100157560629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30023935327725600420161677 11258975747897100157560629)
                  ·
                    refine ⟨1055528976365353139771309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11258975747897100157560629 1055528976365353139771309)
                    ·
                      rfl

theorem cell22_3083453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3083453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083453 prefixEnd_3083453 := by exact prefixLift 3083453
  have htrace : WordTrace (prefixWord ++ tailWord_3083453) baseStart_3083453 baseEnd_3083453 := by
    simpa [prefixWord, tailWord_3083453, baseEnd_3083453] using wordTrace_append hprefix tailTrace_3083453
  have hstable : (prefixWord ++ tailWord_3083453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083453).length < 2 ^ (prefixWord ++ tailWord_3083453).sum := by decide
  have hdescent : baseEnd_3083453 < baseStart_3083453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083455 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 4]
def baseStart_3083455 : Nat := 118140960795 + 3083455 * 2 ^ 59
def prefixEnd_3083455 : Nat := 4983230072969 + 3 ^ 40 * 3083455 * 2
def baseEnd_3083455 : Nat := 351843220335408600407101

theorem tailTrace_3083455 : CollatzResearch.WordTrace tailWord_3083455 prefixEnd_3083455 351843220335408600407101 := by
  unfold tailWord_3083455
  simp only [CollatzResearch.WordTrace]
  refine ⟨112462843044176622033371819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74975228696117748022247879 112462843044176622033371819)
  ·
    refine ⟨168694264566264933050057729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112462843044176622033371819 168694264566264933050057729)
    ·
      refine ⟨126520698424698699787543297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168694264566264933050057729 126520698424698699787543297)
      ·
        refine ⟨94890523818524024840657473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126520698424698699787543297 94890523818524024840657473)
        ·
          refine ⟨71167892863893018630493105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94890523818524024840657473 71167892863893018630493105)
          ·
            refine ⟨53375919647919763972869829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71167892863893018630493105 53375919647919763972869829)
            ·
              refine ⟨10007984933984955744913093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53375919647919763972869829 10007984933984955744913093)
              ·
                refine ⟨1876497175122179202171205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10007984933984955744913093 1876497175122179202171205)
                ·
                  refine ⟨351843220335408600407101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876497175122179202171205 351843220335408600407101)
                  ·
                    rfl

theorem cell22_3083455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4].length) (baseStart_3083455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083455 prefixEnd_3083455 := by exact prefixLift 3083455
  have htrace : WordTrace (prefixWord ++ tailWord_3083455) baseStart_3083455 baseEnd_3083455 := by
    simpa [prefixWord, tailWord_3083455, baseEnd_3083455] using wordTrace_append hprefix tailTrace_3083455
  have hstable : (prefixWord ++ tailWord_3083455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083455).length < 2 ^ (prefixWord ++ tailWord_3083455).sum := by decide
  have hdescent : baseEnd_3083455 < baseStart_3083455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083513 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_3083513 : Nat := 118140960795 + 3083513 * 2 ^ 59
def prefixEnd_3083513 : Nat := 4983230072969 + 3 ^ 40 * 3083513 * 2
def baseEnd_3083513 : Nat := 1055549515591532983271125

theorem tailTrace_3083513 : CollatzResearch.WordTrace tailWord_3083513 prefixEnd_3083513 1055549515591532983271125 := by
  unfold tailWord_3083513
  simp only [CollatzResearch.WordTrace]
  refine ⟨112464958477966497938983193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74976638985310998625988795 112464958477966497938983193)
  ·
    refine ⟨84348718858474873454237395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112464958477966497938983193 84348718858474873454237395)
    ·
      refine ⟨126523078287712310181356093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84348718858474873454237395 126523078287712310181356093)
      ·
        refine ⟨47446154357892116318008535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126523078287712310181356093 47446154357892116318008535)
        ·
          refine ⟨71169231536838174477012803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47446154357892116318008535 71169231536838174477012803)
          ·
            refine ⟨106753847305257261715519205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71169231536838174477012803 106753847305257261715519205)
            ·
              refine ⟨20016346369735736571659851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106753847305257261715519205 20016346369735736571659851)
              ·
                refine ⟨30024519554603604857489777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20016346369735736571659851 30024519554603604857489777)
                ·
                  refine ⟨22518389665952703643117333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30024519554603604857489777 22518389665952703643117333)
                  ·
                    refine ⟨1055549515591532983271125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22518389665952703643117333 1055549515591532983271125)
                    ·
                      rfl

theorem cell22_3083513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_3083513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083513 prefixEnd_3083513 := by exact prefixLift 3083513
  have htrace : WordTrace (prefixWord ++ tailWord_3083513) baseStart_3083513 baseEnd_3083513 := by
    simpa [prefixWord, tailWord_3083513, baseEnd_3083513] using wordTrace_append hprefix tailTrace_3083513
  have hstable : (prefixWord ++ tailWord_3083513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083513).length < 2 ^ (prefixWord ++ tailWord_3083513).sum := by decide
  have hdescent : baseEnd_3083513 < baseStart_3083513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083562 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_3083562 : Nat := 118140960795 + 3083562 * 2 ^ 59
def prefixEnd_3083562 : Nat := 4983230072969 + 3 ^ 40 * 3083562 * 2
def baseEnd_3083562 : Nat := 351855429764304396265325

theorem tailTrace_3083562 : CollatzResearch.WordTrace tailWord_3083562 prefixEnd_3083562 351855429764304396265325 := by
  unfold tailWord_3083562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28116686413697244826879235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74977830436525986205011293 28116686413697244826879235)
  ·
    refine ⟨42175029620545867240318853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28116686413697244826879235 42175029620545867240318853)
    ·
      refine ⟨7907818053852350107559785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42175029620545867240318853 7907818053852350107559785)
      ·
        refine ⟨5930863540389262580669839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7907818053852350107559785 5930863540389262580669839)
        ·
          refine ⟨8896295310583893871004759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930863540389262580669839 8896295310583893871004759)
          ·
            refine ⟨13344442965875840806507139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8896295310583893871004759 13344442965875840806507139)
            ·
              refine ⟨20016664448813761209760709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13344442965875840806507139 20016664448813761209760709)
              ·
                refine ⟨3753124584152580226830133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20016664448813761209760709 3753124584152580226830133)
                ·
                  refine ⟨351855429764304396265325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753124584152580226830133 351855429764304396265325)
                  ·
                    rfl

theorem cell22_3083562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_3083562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083562 prefixEnd_3083562 := by exact prefixLift 3083562
  have htrace : WordTrace (prefixWord ++ tailWord_3083562) baseStart_3083562 baseEnd_3083562 := by
    simpa [prefixWord, tailWord_3083562, baseEnd_3083562] using wordTrace_append hprefix tailTrace_3083562
  have hstable : (prefixWord ++ tailWord_3083562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083562).length < 2 ^ (prefixWord ++ tailWord_3083562).sum := by decide
  have hdescent : baseEnd_3083562 < baseStart_3083562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083577 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_3083577 : Nat := 118140960795 + 3083577 * 2 ^ 59
def prefixEnd_3083577 : Nat := 4983230072969 + 3 ^ 40 * 3083577 * 2
def baseEnd_3083577 : Nat := 1055571424099458149670929

theorem tailTrace_3083577 : CollatzResearch.WordTrace tailWord_3083577 prefixEnd_3083577 1055571424099458149670929 := by
  unfold tailWord_3083577
  simp only [CollatzResearch.WordTrace]
  refine ⟨112467292749734636869312985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74978195166489757912875323 112467292749734636869312985)
  ·
    refine ⟨84350469562300977651984739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112467292749734636869312985 84350469562300977651984739)
    ·
      refine ⟨126525704343451466477977109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84350469562300977651984739 126525704343451466477977109)
      ·
        refine ⟨5930892391099287491155177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126525704343451466477977109 5930892391099287491155177)
        ·
          refine ⟨4448169293324465618366383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930892391099287491155177 4448169293324465618366383)
          ·
            refine ⟨6672253939986698427549575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448169293324465618366383 6672253939986698427549575)
            ·
              refine ⟨10008380909980047641324363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672253939986698427549575 10008380909980047641324363)
              ·
                refine ⟨15012571364970071461986545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10008380909980047641324363 15012571364970071461986545)
                ·
                  refine ⟨11259428523727553596489909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15012571364970071461986545 11259428523727553596489909)
                  ·
                    refine ⟨1055571424099458149670929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11259428523727553596489909 1055571424099458149670929)
                    ·
                      rfl

theorem cell22_3083577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_3083577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083577 prefixEnd_3083577 := by exact prefixLift 3083577
  have htrace : WordTrace (prefixWord ++ tailWord_3083577) baseStart_3083577 baseEnd_3083577 := by
    simpa [prefixWord, tailWord_3083577, baseEnd_3083577] using wordTrace_append hprefix tailTrace_3083577
  have hstable : (prefixWord ++ tailWord_3083577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083577).length < 2 ^ (prefixWord ++ tailWord_3083577).sum := by decide
  have hdescent : baseEnd_3083577 < baseStart_3083577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083607 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 4]
def baseStart_3083607 : Nat := 118140960795 + 3083607 * 2 ^ 59
def prefixEnd_3083607 : Nat := 4983230072969 + 3 ^ 40 * 3083607 * 2
def baseEnd_3083607 : Nat := 351860564570849357140279

theorem tailTrace_3083607 : CollatzResearch.WordTrace tailWord_3083607 prefixEnd_3083607 351860564570849357140279 := by
  unfold tailWord_3083607
  simp only [CollatzResearch.WordTrace]
  refine ⟨112468386939625951992905075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74978924626417301328603383 112468386939625951992905075)
  ·
    refine ⟨168702580409438927989357613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112468386939625951992905075 168702580409438927989357613)
    ·
      refine ⟨63263467653539597996009105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168702580409438927989357613 63263467653539597996009105)
      ·
        refine ⟨47447600740154698497006829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63263467653539597996009105 47447600740154698497006829)
        ·
          refine ⟨17792850277558011936377561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47447600740154698497006829 17792850277558011936377561)
          ·
            refine ⟨13344637708168508952283171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17792850277558011936377561 13344637708168508952283171)
            ·
              refine ⟨20016956562252763428424757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13344637708168508952283171 20016956562252763428424757)
              ·
                refine ⟨1876589677711196571414821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20016956562252763428424757 1876589677711196571414821)
                ·
                  refine ⟨351860564570849357140279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876589677711196571414821 351860564570849357140279)
                  ·
                    rfl

theorem cell22_3083607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 4].length) (baseStart_3083607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083607 prefixEnd_3083607 := by exact prefixLift 3083607
  have htrace : WordTrace (prefixWord ++ tailWord_3083607) baseStart_3083607 baseEnd_3083607 := by
    simpa [prefixWord, tailWord_3083607, baseEnd_3083607] using wordTrace_append hprefix tailTrace_3083607
  have hstable : (prefixWord ++ tailWord_3083607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083607).length < 2 ^ (prefixWord ++ tailWord_3083607).sum := by decide
  have hdescent : baseEnd_3083607 < baseStart_3083607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083613 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3083613 : Nat := 118140960795 + 3083613 * 2 ^ 59
def prefixEnd_3083613 : Nat := 4983230072969 + 3 ^ 40 * 3083613 * 2
def baseEnd_3083613 : Nat := 351861249211722018590273

theorem tailTrace_3083613 : CollatzResearch.WordTrace tailWord_3083613 prefixEnd_3083613 351861249211722018590273 := by
  unfold tailWord_3083613
  simp only [CollatzResearch.WordTrace]
  refine ⟨112468605777604215017623493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74979070518402810011748995 112468605777604215017623493)
  ·
    refine ⟨21087863583300790315804405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112468605777604215017623493 21087863583300790315804405)
    ·
      refine ⟨1976987210934449092106663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21087863583300790315804405 1976987210934449092106663)
      ·
        refine ⟨2965480816401673638159995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976987210934449092106663 2965480816401673638159995)
        ·
          refine ⟨4448221224602510457239993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965480816401673638159995 4448221224602510457239993)
          ·
            refine ⟨3336165918451882842929995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448221224602510457239993 3336165918451882842929995)
            ·
              refine ⟨5004248877677824264394993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336165918451882842929995 5004248877677824264394993)
              ·
                refine ⟨3753186658258368198296245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004248877677824264394993 3753186658258368198296245)
                ·
                  refine ⟨351861249211722018590273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753186658258368198296245 351861249211722018590273)
                  ·
                    rfl

theorem cell22_3083613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3083613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083613 prefixEnd_3083613 := by exact prefixLift 3083613
  have htrace : WordTrace (prefixWord ++ tailWord_3083613) baseStart_3083613 baseEnd_3083613 := by
    simpa [prefixWord, tailWord_3083613, baseEnd_3083613] using wordTrace_append hprefix tailTrace_3083613
  have hstable : (prefixWord ++ tailWord_3083613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083613).length < 2 ^ (prefixWord ++ tailWord_3083613).sum := by decide
  have hdescent : baseEnd_3083613 < baseStart_3083613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083639 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 2, 3]
def baseStart_3083639 : Nat := 118140960795 + 3083639 * 2 ^ 59
def prefixEnd_3083639 : Nat := 4983230072969 + 3 ^ 40 * 3083639 * 2
def baseEnd_3083639 : Nat := 1055592647966510654620739

theorem tailTrace_3083639 : CollatzResearch.WordTrace tailWord_3083639 prefixEnd_3083639 1055592647966510654620739 := by
  unfold tailWord_3083639
  simp only [CollatzResearch.WordTrace]
  refine ⟨112469554075510021458069971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74979702717006680972046647 112469554075510021458069971)
  ·
    refine ⟨168704331113265032187104957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112469554075510021458069971 168704331113265032187104957)
    ·
      refine ⟨63264124167474387070164359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168704331113265032187104957 63264124167474387070164359)
      ·
        refine ⟨94896186251211580605246539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63264124167474387070164359 94896186251211580605246539)
        ·
          refine ⟨142344279376817370907869809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94896186251211580605246539 142344279376817370907869809)
          ·
            refine ⟨106758209532613028180902357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142344279376817370907869809 106758209532613028180902357)
            ·
              refine ⟨2502145535920617847989899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 106758209532613028180902357 2502145535920617847989899)
              ·
                refine ⟨3753218303880926771984849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502145535920617847989899 3753218303880926771984849)
                ·
                  refine ⟨2814913727910695078988637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753218303880926771984849 2814913727910695078988637)
                  ·
                    refine ⟨1055592647966510654620739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814913727910695078988637 1055592647966510654620739)
                    ·
                      rfl

theorem cell22_3083639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_3083639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083639 prefixEnd_3083639 := by exact prefixLift 3083639
  have htrace : WordTrace (prefixWord ++ tailWord_3083639) baseStart_3083639 baseEnd_3083639 := by
    simpa [prefixWord, tailWord_3083639, baseEnd_3083639] using wordTrace_append hprefix tailTrace_3083639
  have hstable : (prefixWord ++ tailWord_3083639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083639).length < 2 ^ (prefixWord ++ tailWord_3083639).sum := by decide
  have hdescent : baseEnd_3083639 < baseStart_3083639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083652 : List Nat := [2, 3, 2, 1, 1, 3, 4, 6]
def baseStart_3083652 : Nat := 118140960795 + 3083652 * 2 ^ 59
def prefixEnd_3083652 : Nat := 4983230072969 + 3 ^ 40 * 3083652 * 2
def baseEnd_3083652 : Nat := 117288566459131439338411

theorem tailTrace_3083652 : CollatzResearch.WordTrace tailWord_3083652 prefixEnd_3083652 117288566459131439338411 := by
  unfold tailWord_3083652
  simp only [CollatzResearch.WordTrace]
  refine ⟨56235014112231462339146605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74980018816308616452195473 56235014112231462339146605)
  ·
    refine ⟨21088130292086798377179977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56235014112231462339146605 21088130292086798377179977)
    ·
      refine ⟨15816097719065098782884983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21088130292086798377179977 15816097719065098782884983)
      ·
        refine ⟨23724146578597648174327475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15816097719065098782884983 23724146578597648174327475)
        ·
          refine ⟨35586219867896472261491213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23724146578597648174327475 35586219867896472261491213)
          ·
            refine ⟨13344832450461177098059205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35586219867896472261491213 13344832450461177098059205)
            ·
              refine ⟨2502156084461470705886101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13344832450461177098059205 2502156084461470705886101)
              ·
                refine ⟨117288566459131439338411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2502156084461470705886101 117288566459131439338411)
                ·
                  rfl

theorem cell22_3083652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_3083652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083652 prefixEnd_3083652 := by exact prefixLift 3083652
  have htrace : WordTrace (prefixWord ++ tailWord_3083652) baseStart_3083652 baseEnd_3083652 := by
    simpa [prefixWord, tailWord_3083652, baseEnd_3083652] using wordTrace_append hprefix tailTrace_3083652
  have hstable : (prefixWord ++ tailWord_3083652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083652).length < 2 ^ (prefixWord ++ tailWord_3083652).sum := by decide
  have hdescent : baseEnd_3083652 < baseStart_3083652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083680 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_3083680 : Nat := 118140960795 + 3083680 * 2 ^ 59
def prefixEnd_3083680 : Nat := 4983230072969 + 3 ^ 40 * 3083680 * 2
def baseEnd_3083680 : Nat := 351868894368133404781871

theorem tailTrace_3083680 : CollatzResearch.WordTrace tailWord_3083680 prefixEnd_3083680 351868894368133404781871 := by
  unfold tailWord_3083680
  simp only [CollatzResearch.WordTrace]
  refine ⟨56235524734180742730156247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74980699645574323640208329 56235524734180742730156247)
  ·
    refine ⟨84353287101271114095234371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56235524734180742730156247 84353287101271114095234371)
    ·
      refine ⟨126529930651906671142851557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84353287101271114095234371 126529930651906671142851557)
      ·
        refine ⟨23724361997232500839284667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126529930651906671142851557 23724361997232500839284667)
        ·
          refine ⟨35586542995848751258927001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23724361997232500839284667 35586542995848751258927001)
          ·
            refine ⟨26689907246886563444195251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35586542995848751258927001 26689907246886563444195251)
            ·
              refine ⟨40034860870329845166292877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26689907246886563444195251 40034860870329845166292877)
              ·
                refine ⟨15013072826373691937359829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40034860870329845166292877 15013072826373691937359829)
                ·
                  refine ⟨351868894368133404781871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15013072826373691937359829 351868894368133404781871)
                  ·
                    rfl

theorem cell22_3083680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_3083680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083680 prefixEnd_3083680 := by exact prefixLift 3083680
  have htrace : WordTrace (prefixWord ++ tailWord_3083680) baseStart_3083680 baseEnd_3083680 := by
    simpa [prefixWord, tailWord_3083680, baseEnd_3083680] using wordTrace_append hprefix tailTrace_3083680
  have hstable : (prefixWord ++ tailWord_3083680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083680).length < 2 ^ (prefixWord ++ tailWord_3083680).sum := by decide
  have hdescent : baseEnd_3083680 < baseStart_3083680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083695 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3083695 : Nat := 118140960795 + 3083695 * 2 ^ 59
def prefixEnd_3083695 : Nat := 4983230072969 + 3 ^ 40 * 3083695 * 2
def baseEnd_3083695 : Nat := 1055611817910945175220567

theorem tailTrace_3083695 : CollatzResearch.WordTrace tailWord_3083695 prefixEnd_3083695 1055611817910945175220567 := by
  unfold tailWord_3083695
  simp only [CollatzResearch.WordTrace]
  refine ⟨112471596563307143022108539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74981064375538095348072359 112471596563307143022108539)
  ·
    refine ⟨168707394844960714533162809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112471596563307143022108539 168707394844960714533162809)
    ·
      refine ⟨126530546133720535899872107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168707394844960714533162809 126530546133720535899872107)
      ·
        refine ⟨189795819200580803849808161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126530546133720535899872107 189795819200580803849808161)
        ·
          refine ⟨142346864400435602887356121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189795819200580803849808161 142346864400435602887356121)
          ·
            refine ⟨106760148300326702165517091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142346864400435602887356121 106760148300326702165517091)
            ·
              refine ⟨160140222450490053248275637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106760148300326702165517091 160140222450490053248275637)
              ·
                refine ⟨15013145854733442492025841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160140222450490053248275637 15013145854733442492025841)
                ·
                  refine ⟨11259859391050081869019381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15013145854733442492025841 11259859391050081869019381)
                  ·
                    refine ⟨1055611817910945175220567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11259859391050081869019381 1055611817910945175220567)
                    ·
                      rfl

theorem cell22_3083695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3083695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083695 prefixEnd_3083695 := by exact prefixLift 3083695
  have htrace : WordTrace (prefixWord ++ tailWord_3083695) baseStart_3083695 baseEnd_3083695 := by
    simpa [prefixWord, tailWord_3083695, baseEnd_3083695] using wordTrace_append hprefix tailTrace_3083695
  have hstable : (prefixWord ++ tailWord_3083695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083695).length < 2 ^ (prefixWord ++ tailWord_3083695).sum := by decide
  have hdescent : baseEnd_3083695 < baseStart_3083695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083697 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 5]
def baseStart_3083697 : Nat := 118140960795 + 3083697 * 2 ^ 59
def prefixEnd_3083697 : Nat := 4983230072969 + 3 ^ 40 * 3083697 * 2
def baseEnd_3083697 : Nat := 351870834183939278890187

theorem tailTrace_3083697 : CollatzResearch.WordTrace tailWord_3083697 prefixEnd_3083697 351870834183939278890187 := by
  unfold tailWord_3083697
  simp only [CollatzResearch.WordTrace]
  refine ⟨112471669509299897363681345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74981113006199931575787563 112471669509299897363681345)
  ·
    refine ⟨84353752131974923022761009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112471669509299897363681345 84353752131974923022761009)
    ·
      refine ⟨63265314098981192267070757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84353752131974923022761009 63265314098981192267070757)
      ·
        refine ⟨11862246393558973550075767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63265314098981192267070757 11862246393558973550075767)
        ·
          refine ⟨17793369590338460325113651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862246393558973550075767 17793369590338460325113651)
          ·
            refine ⟨26690054385507690487670477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17793369590338460325113651 26690054385507690487670477)
            ·
              refine ⟨10008770394565383932876429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26690054385507690487670477 10008770394565383932876429)
              ·
                refine ⟨3753288897962018974828661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10008770394565383932876429 3753288897962018974828661)
                ·
                  refine ⟨351870834183939278890187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753288897962018974828661 351870834183939278890187)
                  ·
                    rfl

theorem cell22_3083697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_3083697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083697 prefixEnd_3083697 := by exact prefixLift 3083697
  have htrace : WordTrace (prefixWord ++ tailWord_3083697) baseStart_3083697 baseEnd_3083697 := by
    simpa [prefixWord, tailWord_3083697, baseEnd_3083697] using wordTrace_append hprefix tailTrace_3083697
  have hstable : (prefixWord ++ tailWord_3083697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083697).length < 2 ^ (prefixWord ++ tailWord_3083697).sum := by decide
  have hdescent : baseEnd_3083697 < baseStart_3083697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083727 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 1, 4]
def baseStart_3083727 : Nat := 118140960795 + 3083727 * 2 ^ 59
def prefixEnd_3083727 : Nat := 4983230072969 + 3 ^ 40 * 3083727 * 2
def baseEnd_3083727 : Nat := 1055622772164907758420469

theorem tailTrace_3083727 : CollatzResearch.WordTrace tailWord_3083727 prefixEnd_3083727 1055622772164907758420469 := by
  unfold tailWord_3083727
  simp only [CollatzResearch.WordTrace]
  refine ⟨112472763699191212487273435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74981842466127474991515623 112472763699191212487273435)
  ·
    refine ⟨168709145548786818730910153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112472763699191212487273435 168709145548786818730910153)
    ·
      refine ⟨126531859161590114048182615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168709145548786818730910153 126531859161590114048182615)
      ·
        refine ⟨189797788742385171072273923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126531859161590114048182615 189797788742385171072273923)
        ·
          refine ⟨284696683113577756608410885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189797788742385171072273923 284696683113577756608410885)
          ·
            refine ⟨53380628083795829364077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284696683113577756608410885 53380628083795829364077041)
            ·
              refine ⟨40035471062846872023057781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53380628083795829364077041 40035471062846872023057781)
              ·
                refine ⟨3753325412141894252161667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40035471062846872023057781 3753325412141894252161667)
                ·
                  refine ⟨5629988118212841378242501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753325412141894252161667 5629988118212841378242501)
                  ·
                    refine ⟨1055622772164907758420469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629988118212841378242501 1055622772164907758420469)
                    ·
                      rfl

theorem cell22_3083727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_3083727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083727 prefixEnd_3083727 := by exact prefixLift 3083727
  have htrace : WordTrace (prefixWord ++ tailWord_3083727) baseStart_3083727 baseEnd_3083727 := by
    simpa [prefixWord, tailWord_3083727, baseEnd_3083727] using wordTrace_append hprefix tailTrace_3083727
  have hstable : (prefixWord ++ tailWord_3083727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083727).length < 2 ^ (prefixWord ++ tailWord_3083727).sum := by decide
  have hdescent : baseEnd_3083727 < baseStart_3083727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083778 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3083778 : Nat := 118140960795 + 3083778 * 2 ^ 59
def prefixEnd_3083778 : Nat := 4983230072969 + 3 ^ 40 * 3083778 * 2
def baseEnd_3083778 : Nat := 1055640230507160625395313

theorem tailTrace_3083778 : CollatzResearch.WordTrace tailWord_3083778 prefixEnd_3083778 1055640230507160625395313 := by
  unfold tailWord_3083778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28118655955501612049344997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74983082548004298798253325 28118655955501612049344997)
  ·
    refine ⟨5272247991656552259252187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28118655955501612049344997 5272247991656552259252187)
    ·
      refine ⟨7908371987484828388878281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272247991656552259252187 7908371987484828388878281)
      ·
        refine ⟨5931278990613621291658711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7908371987484828388878281 5931278990613621291658711)
        ·
          refine ⟨8896918485920431937488067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5931278990613621291658711 8896918485920431937488067)
          ·
            refine ⟨13345377728880647906232101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8896918485920431937488067 13345377728880647906232101)
            ·
              refine ⟨2502258324165121482418519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13345377728880647906232101 2502258324165121482418519)
              ·
                refine ⟨3753387486247682223627779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502258324165121482418519 3753387486247682223627779)
                ·
                  refine ⟨5630081229371523335441669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753387486247682223627779 5630081229371523335441669)
                  ·
                    refine ⟨1055640230507160625395313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630081229371523335441669 1055640230507160625395313)
                    ·
                      rfl

theorem cell22_3083778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3083778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083778 prefixEnd_3083778 := by exact prefixLift 3083778
  have htrace : WordTrace (prefixWord ++ tailWord_3083778) baseStart_3083778 baseEnd_3083778 := by
    simpa [prefixWord, tailWord_3083778, baseEnd_3083778] using wordTrace_append hprefix tailTrace_3083778
  have hstable : (prefixWord ++ tailWord_3083778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083778).length < 2 ^ (prefixWord ++ tailWord_3083778).sum := by decide
  have hdescent : baseEnd_3083778 < baseStart_3083778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083782 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3083782 : Nat := 118140960795 + 3083782 * 2 ^ 59
def prefixEnd_3083782 : Nat := 4983230072969 + 3 ^ 40 * 3083782 * 2
def baseEnd_3083782 : Nat := 351880533262968649431767

theorem tailTrace_3083782 : CollatzResearch.WordTrace tailWord_3083782 prefixEnd_3083782 351880533262968649431767 := by
  unfold tailWord_3083782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514836553562248652516425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74983179809327971253683733 3514836553562248652516425)
  ·
    refine ⟨2636127415171686489387319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3514836553562248652516425 2636127415171686489387319)
    ·
      refine ⟨3954191122757529734080979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636127415171686489387319 3954191122757529734080979)
      ·
        refine ⟨5931286684136294601121469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954191122757529734080979 5931286684136294601121469)
        ·
          refine ⟨2224232506551110475420551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5931286684136294601121469 2224232506551110475420551)
          ·
            refine ⟨3336348759826665713130827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224232506551110475420551 3336348759826665713130827)
            ·
              refine ⟨5004523139739998569696241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336348759826665713130827 5004523139739998569696241)
              ·
                refine ⟨3753392354804998927272181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004523139739998569696241 3753392354804998927272181)
                ·
                  refine ⟨351880533262968649431767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753392354804998927272181 351880533262968649431767)
                  ·
                    rfl

theorem cell22_3083782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3083782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083782 prefixEnd_3083782 := by exact prefixLift 3083782
  have htrace : WordTrace (prefixWord ++ tailWord_3083782) baseStart_3083782 baseEnd_3083782 := by
    simpa [prefixWord, tailWord_3083782, baseEnd_3083782] using wordTrace_append hprefix tailTrace_3083782
  have hstable : (prefixWord ++ tailWord_3083782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083782).length < 2 ^ (prefixWord ++ tailWord_3083782).sum := by decide
  have hdescent : baseEnd_3083782 < baseStart_3083782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083787 : List Nat := [1, 1, 1, 1, 8, 1, 9]
def baseStart_3083787 : Nat := 118140960795 + 3083787 * 2 ^ 59
def prefixEnd_3083787 : Nat := 4983230072969 + 3 ^ 40 * 3083787 * 2
def baseEnd_3083787 : Nat := 39097900421892133404455

theorem tailTrace_3083787 : CollatzResearch.WordTrace tailWord_3083787 prefixEnd_3083787 39097900421892133404455 := by
  unfold tailWord_3083787
  simp only [CollatzResearch.WordTrace]
  refine ⟨112474952078973842734457615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74983301385982561822971743 112474952078973842734457615)
  ·
    refine ⟨168712428118460764101686423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112474952078973842734457615 168712428118460764101686423)
    ·
      refine ⟨253068642177691146152529635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168712428118460764101686423 253068642177691146152529635)
      ·
        refine ⟨379602963266536719228794453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253068642177691146152529635 379602963266536719228794453)
        ·
          refine ⟨4448472225779727178462435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 379602963266536719228794453 4448472225779727178462435)
          ·
            refine ⟨6672708338669590767693653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448472225779727178462435 6672708338669590767693653)
            ·
              refine ⟨39097900421892133404455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6672708338669590767693653 39097900421892133404455)
              ·
                rfl

theorem cell22_3083787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 9].length) (baseStart_3083787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083787 prefixEnd_3083787 := by exact prefixLift 3083787
  have htrace : WordTrace (prefixWord ++ tailWord_3083787) baseStart_3083787 baseEnd_3083787 := by
    simpa [prefixWord, tailWord_3083787, baseEnd_3083787] using wordTrace_append hprefix tailTrace_3083787
  have hstable : (prefixWord ++ tailWord_3083787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083787).length < 2 ^ (prefixWord ++ tailWord_3083787).sum := by decide
  have hdescent : baseEnd_3083787 < baseStart_3083787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083808 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_3083808 : Nat := 118140960795 + 3083808 * 2 ^ 59
def prefixEnd_3083808 : Nat := 4983230072969 + 3 ^ 40 * 3083808 * 2
def baseEnd_3083808 : Nat := 1055650500120250547145221

theorem tailTrace_3083808 : CollatzResearch.WordTrace tailWord_3083808 prefixEnd_3083808 1055650500120250547145221 := by
  unfold tailWord_3083808
  simp only [CollatzResearch.WordTrace]
  refine ⟨56237859005948881660486039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74983812007931842213981385 56237859005948881660486039)
  ·
    refine ⟨84356788508923322490729059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56237859005948881660486039 84356788508923322490729059)
    ·
      refine ⟨126535182763384983736093589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84356788508923322490729059 126535182763384983736093589)
      ·
        refine ⟨5931336692033671112629387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126535182763384983736093589 5931336692033671112629387)
        ·
          refine ⟨8897005038050506668944081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5931336692033671112629387 8897005038050506668944081)
          ·
            refine ⟨6672753778537880001708061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8897005038050506668944081 6672753778537880001708061)
            ·
              refine ⟨2502282666951705000640523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6672753778537880001708061 2502282666951705000640523)
              ·
                refine ⟨3753424000427557500960785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502282666951705000640523 3753424000427557500960785)
                ·
                  refine ⟨2815068000320668125720589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753424000427557500960785 2815068000320668125720589)
                  ·
                    refine ⟨1055650500120250547145221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815068000320668125720589 1055650500120250547145221)
                    ·
                      rfl

theorem cell22_3083808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_3083808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083808 prefixEnd_3083808 := by exact prefixLift 3083808
  have htrace : WordTrace (prefixWord ++ tailWord_3083808) baseStart_3083808 baseEnd_3083808 := by
    simpa [prefixWord, tailWord_3083808, baseEnd_3083808] using wordTrace_append hprefix tailTrace_3083808
  have hstable : (prefixWord ++ tailWord_3083808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083808).length < 2 ^ (prefixWord ++ tailWord_3083808).sum := by decide
  have hdescent : baseEnd_3083808 < baseStart_3083808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083832 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_3083832 : Nat := 118140960795 + 3083832 * 2 ^ 59
def prefixEnd_3083832 : Nat := 4983230072969 + 3 ^ 40 * 3083832 * 2
def baseEnd_3083832 : Nat := 351886238603574161515049

theorem tailTrace_3083832 : CollatzResearch.WordTrace tailWord_3083832 prefixEnd_3083832 351886238603574161515049 := by
  unfold tailWord_3083832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56238296681905407709922875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74984395575873876946563833 56238296681905407709922875)
  ·
    refine ⟨84357445022858111564884313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56238296681905407709922875 84357445022858111564884313)
    ·
      refine ⟨63268083767143583673663235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84357445022858111564884313 63268083767143583673663235)
      ·
        refine ⟨94902125650715375510494853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63268083767143583673663235 94902125650715375510494853)
        ·
          refine ⟨17794148559509132908217785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94902125650715375510494853 17794148559509132908217785)
          ·
            refine ⟨13345611419631849681163339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17794148559509132908217785 13345611419631849681163339)
            ·
              refine ⟨20018417129447774521745009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13345611419631849681163339 20018417129447774521745009)
              ·
                refine ⟨15013812847085830891308757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20018417129447774521745009 15013812847085830891308757)
                ·
                  refine ⟨351886238603574161515049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15013812847085830891308757 351886238603574161515049)
                  ·
                    rfl

theorem cell22_3083832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_3083832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083832 prefixEnd_3083832 := by exact prefixLift 3083832
  have htrace : WordTrace (prefixWord ++ tailWord_3083832) baseStart_3083832 baseEnd_3083832 := by
    simpa [prefixWord, tailWord_3083832, baseEnd_3083832] using wordTrace_append hprefix tailTrace_3083832
  have hstable : (prefixWord ++ tailWord_3083832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083832).length < 2 ^ (prefixWord ++ tailWord_3083832).sum := by decide
  have hdescent : baseEnd_3083832 < baseStart_3083832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083907 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_3083907 : Nat := 118140960795 + 3083907 * 2 ^ 59
def prefixEnd_3083907 : Nat := 4983230072969 + 3 ^ 40 * 3083907 * 2
def baseEnd_3083907 : Nat := 1055684389843447288919917

theorem tailTrace_3083907 : CollatzResearch.WordTrace tailWord_3083907 prefixEnd_3083907 1055684389843447288919917 := by
  unfold tailWord_3083907
  simp only [CollatzResearch.WordTrace]
  refine ⟨112479328838539103228825975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74986219225692735485883983 112479328838539103228825975)
  ·
    refine ⟨168718993257808654843238963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112479328838539103228825975 168718993257808654843238963)
    ·
      refine ⟨253078489886712982264858445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168718993257808654843238963 253078489886712982264858445)
      ·
        refine ⟨94904433707517368349321917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253078489886712982264858445 94904433707517368349321917)
        ·
          refine ⟨35589162640319013130995719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94904433707517368349321917 35589162640319013130995719)
          ·
            refine ⟨53383743960478519696493579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35589162640319013130995719 53383743960478519696493579)
            ·
              refine ⟨80075615940717779544740369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53383743960478519696493579 80075615940717779544740369)
              ·
                refine ⟨60056711955538334658555277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80075615940717779544740369 60056711955538334658555277)
                ·
                  refine ⟨22521266983326875496958229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60056711955538334658555277 22521266983326875496958229)
                  ·
                    refine ⟨1055684389843447288919917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22521266983326875496958229 1055684389843447288919917)
                    ·
                      rfl

theorem cell22_3083907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_3083907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083907 prefixEnd_3083907 := by exact prefixLift 3083907
  have htrace : WordTrace (prefixWord ++ tailWord_3083907) baseStart_3083907 baseEnd_3083907 := by
    simpa [prefixWord, tailWord_3083907, baseEnd_3083907] using wordTrace_append hprefix tailTrace_3083907
  have hstable : (prefixWord ++ tailWord_3083907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083907).length < 2 ^ (prefixWord ++ tailWord_3083907).sum := by decide
  have hdescent : baseEnd_3083907 < baseStart_3083907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083911 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 4]
def baseStart_3083911 : Nat := 118140960795 + 3083911 * 2 ^ 59
def prefixEnd_3083911 : Nat := 4983230072969 + 3 ^ 40 * 3083911 * 2
def baseEnd_3083911 : Nat := 351895253041730870606635

theorem tailTrace_3083911 : CollatzResearch.WordTrace tailWord_3083911 prefixEnd_3083911 351895253041730870606635 := by
  unfold tailWord_3083911
  simp only [CollatzResearch.WordTrace]
  refine ⟨112479474730524611911971587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74986316487016407941314391 112479474730524611911971587)
  ·
    refine ⟨168719212095786917867957381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112479474730524611911971587 168719212095786917867957381)
    ·
      refine ⟨31634852267960047100242009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168719212095786917867957381 31634852267960047100242009)
      ·
        refine ⟨23726139200970035325181507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31634852267960047100242009 23726139200970035325181507)
        ·
          refine ⟨35589208801455052987772261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23726139200970035325181507 35589208801455052987772261)
          ·
            refine ⟨6672976650272822435207299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35589208801455052987772261 6672976650272822435207299)
            ·
              refine ⟨10009464975409233652810949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672976650272822435207299 10009464975409233652810949)
              ·
                refine ⟨1876774682889231309902053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10009464975409233652810949 1876774682889231309902053)
                ·
                  refine ⟨351895253041730870606635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876774682889231309902053 351895253041730870606635)
                  ·
                    rfl

theorem cell22_3083911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 4].length) (baseStart_3083911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083911 prefixEnd_3083911 := by exact prefixLift 3083911
  have htrace : WordTrace (prefixWord ++ tailWord_3083911) baseStart_3083911 baseEnd_3083911 := by
    simpa [prefixWord, tailWord_3083911, baseEnd_3083911] using wordTrace_append hprefix tailTrace_3083911
  have hstable : (prefixWord ++ tailWord_3083911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083911).length < 2 ^ (prefixWord ++ tailWord_3083911).sum := by decide
  have hdescent : baseEnd_3083911 < baseStart_3083911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083939 : List Nat := [1, 1, 1, 4, 1, 1, 7, 6]
def baseStart_3083939 : Nat := 118140960795 + 3083939 * 2 ^ 59
def prefixEnd_3083939 : Nat := 4983230072969 + 3 ^ 40 * 3083939 * 2
def baseEnd_3083939 : Nat := 117299482677489985791091

theorem tailTrace_3083939 : CollatzResearch.WordTrace tailWord_3083939 prefixEnd_3083939 117299482677489985791091 := by
  unfold tailWord_3083939
  simp only [CollatzResearch.WordTrace]
  refine ⟨112480495974423172693990871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74986997316282115129327247 112480495974423172693990871)
  ·
    refine ⟨168720743961634759040986307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112480495974423172693990871 168720743961634759040986307)
    ·
      refine ⟨253081115942452138561479461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168720743961634759040986307 253081115942452138561479461)
      ·
        refine ⟨47452709239209775980277399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253081115942452138561479461 47452709239209775980277399)
        ·
          refine ⟨71179063858814663970416099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47452709239209775980277399 71179063858814663970416099)
          ·
            refine ⟨106768595788221995955624149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71179063858814663970416099 106768595788221995955624149)
            ·
              refine ⟨2502388963786453030209941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 106768595788221995955624149 2502388963786453030209941)
              ·
                refine ⟨117299482677489985791091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2502388963786453030209941 117299482677489985791091)
                ·
                  rfl

theorem cell22_3083939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 6].length) (baseStart_3083939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083939 prefixEnd_3083939 := by exact prefixLift 3083939
  have htrace : WordTrace (prefixWord ++ tailWord_3083939) baseStart_3083939 baseEnd_3083939 := by
    simpa [prefixWord, tailWord_3083939, baseEnd_3083939] using wordTrace_append hprefix tailTrace_3083939
  have hstable : (prefixWord ++ tailWord_3083939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083939).length < 2 ^ (prefixWord ++ tailWord_3083939).sum := by decide
  have hdescent : baseEnd_3083939 < baseStart_3083939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083988 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3083988 : Nat := 118140960795 + 3083988 * 2 ^ 59
def prefixEnd_3083988 : Nat := 4983230072969 + 3 ^ 40 * 3083988 * 2
def baseEnd_3083988 : Nat := 1055712117798790077644669

theorem tailTrace_3083988 : CollatzResearch.WordTrace tailWord_3083988 prefixEnd_3083988 1055712117798790077644669 := by
  unfold tailWord_3083988
  simp only [CollatzResearch.WordTrace]
  refine ⟨56241141575622827031262309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74988188767497102708349745 56241141575622827031262309)
  ·
    refine ⟨10545214045429280068361683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56241141575622827031262309 10545214045429280068361683)
    ·
      refine ⟨15817821068143920102542525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10545214045429280068361683 15817821068143920102542525)
      ·
        refine ⟨5931682900553970038453447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15817821068143920102542525 5931682900553970038453447)
        ·
          refine ⟨8897524350830955057680171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5931682900553970038453447 8897524350830955057680171)
          ·
            refine ⟨13346286526246432586520257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8897524350830955057680171 13346286526246432586520257)
            ·
              refine ⟨10009714894684824439890193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13346286526246432586520257 10009714894684824439890193)
              ·
                refine ⟨7507286171013618329917645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10009714894684824439890193 7507286171013618329917645)
                ·
                  refine ⟨2815232314130106873719117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7507286171013618329917645 2815232314130106873719117)
                  ·
                    refine ⟨1055712117798790077644669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815232314130106873719117 1055712117798790077644669)
                    ·
                      rfl

theorem cell22_3083988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3083988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3083988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3083988 prefixEnd_3083988 := by exact prefixLift 3083988
  have htrace : WordTrace (prefixWord ++ tailWord_3083988) baseStart_3083988 baseEnd_3083988 := by
    simpa [prefixWord, tailWord_3083988, baseEnd_3083988] using wordTrace_append hprefix tailTrace_3083988
  have hstable : (prefixWord ++ tailWord_3083988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083988).length < 2 ^ (prefixWord ++ tailWord_3083988).sum := by decide
  have hdescent : baseEnd_3083988 < baseStart_3083988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084022 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3084022 : Nat := 118140960795 + 3084022 * 2 ^ 59
def prefixEnd_3084022 : Nat := 4983230072969 + 3 ^ 40 * 3084022 * 2
def baseEnd_3084022 : Nat := 1055723756693625322294565

theorem tailTrace_3084022 : CollatzResearch.WordTrace tailWord_3084022 prefixEnd_3084022 1055723756693625322294565 := by
  unfold tailWord_3084022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030220202070154866828895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74989015488748318579508213 7030220202070154866828895)
  ·
    refine ⟨10545330303105232300243343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7030220202070154866828895 10545330303105232300243343)
    ·
      refine ⟨15817995454657848450365015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10545330303105232300243343 15817995454657848450365015)
      ·
        refine ⟨23726993181986772675547523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15817995454657848450365015 23726993181986772675547523)
        ·
          refine ⟨35590489772980159013321285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23726993181986772675547523 35590489772980159013321285)
          ·
            refine ⟨6673216832433779814997741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35590489772980159013321285 6673216832433779814997741)
            ·
              refine ⟨2502456312162667430624153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6673216832433779814997741 2502456312162667430624153)
              ·
                refine ⟨1876842234122000572968115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502456312162667430624153 1876842234122000572968115)
                ·
                  refine ⟨2815263351183000859452173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876842234122000572968115 2815263351183000859452173)
                  ·
                    refine ⟨1055723756693625322294565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815263351183000859452173 1055723756693625322294565)
                    ·
                      rfl

theorem cell22_3084022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3084022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084022 prefixEnd_3084022 := by exact prefixLift 3084022
  have htrace : WordTrace (prefixWord ++ tailWord_3084022) baseStart_3084022 baseEnd_3084022 := by
    simpa [prefixWord, tailWord_3084022, baseEnd_3084022] using wordTrace_append hprefix tailTrace_3084022
  have hstable : (prefixWord ++ tailWord_3084022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084022).length < 2 ^ (prefixWord ++ tailWord_3084022).sum := by decide
  have hdescent : baseEnd_3084022 < baseStart_3084022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084029 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 6]
def baseStart_3084029 : Nat := 118140960795 + 3084029 * 2 ^ 59
def prefixEnd_3084029 : Nat := 4983230072969 + 3 ^ 40 * 3084029 * 2
def baseEnd_3084029 : Nat := 351908717645559879123181

theorem tailTrace_3084029 : CollatzResearch.WordTrace tailWord_3084029 prefixEnd_3084029 351908717645559879123181 := by
  unfold tailWord_3084029
  simp only [CollatzResearch.WordTrace]
  refine ⟨112483778544097118064767141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74989185696064745376511427 112483778544097118064767141)
  ·
    refine ⟨21090708477018209637143839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112483778544097118064767141 21090708477018209637143839)
    ·
      refine ⟨31636062715527314455715759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21090708477018209637143839 31636062715527314455715759)
      ·
        refine ⟨47454094073290971683573639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31636062715527314455715759 47454094073290971683573639)
        ·
          refine ⟨71181141109936457525360459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47454094073290971683573639 71181141109936457525360459)
          ·
            refine ⟨106771711664904686288040689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71181141109936457525360459 106771711664904686288040689)
            ·
              refine ⟨80078783748678514716030517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106771711664904686288040689 80078783748678514716030517)
              ·
                refine ⟨7507385976438610754627861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80078783748678514716030517 7507385976438610754627861)
                ·
                  refine ⟨351908717645559879123181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7507385976438610754627861 351908717645559879123181)
                  ·
                    rfl

theorem cell22_3084029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_3084029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084029 prefixEnd_3084029 := by exact prefixLift 3084029
  have htrace : WordTrace (prefixWord ++ tailWord_3084029) baseStart_3084029 baseEnd_3084029 := by
    simpa [prefixWord, tailWord_3084029, baseEnd_3084029] using wordTrace_append hprefix tailTrace_3084029
  have hstable : (prefixWord ++ tailWord_3084029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084029).length < 2 ^ (prefixWord ++ tailWord_3084029).sum := by decide
  have hdescent : baseEnd_3084029 < baseStart_3084029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_3084059 : Nat := 118140960795 + 3084059 * 2 ^ 59
def prefixEnd_3084059 : Nat := 4983230072969 + 3 ^ 40 * 3084059 * 2
def baseEnd_3084059 : Nat := 1055736422549769559119451

theorem tailTrace_3084059 : CollatzResearch.WordTrace tailWord_3084059 prefixEnd_3084059 1055736422549769559119451 := by
  unfold tailWord_3084059
  simp only [CollatzResearch.WordTrace]
  refine ⟨112484872733988433188359231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74989915155992288792239487 112484872733988433188359231)
  ·
    refine ⟨168727309100982649782538847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112484872733988433188359231 168727309100982649782538847)
    ·
      refine ⟨253090963651473974673808271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168727309100982649782538847 253090963651473974673808271)
      ·
        refine ⟨379636445477210962010712407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253090963651473974673808271 379636445477210962010712407)
        ·
          refine ⟨569454668215816443016068611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379636445477210962010712407 569454668215816443016068611)
          ·
            refine ⟨854182002323724664524102917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569454668215816443016068611 854182002323724664524102917)
            ·
              refine ⟨160159125435698374598269297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 854182002323724664524102917 160159125435698374598269297)
              ·
                refine ⟨120119344076773780948701973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160159125435698374598269297 120119344076773780948701973)
                ·
                  refine ⟨5630594253598770981970405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120119344076773780948701973 5630594253598770981970405)
                  ·
                    refine ⟨1055736422549769559119451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630594253598770981970405 1055736422549769559119451)
                    ·
                      rfl

theorem cell22_3084059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_3084059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084059 prefixEnd_3084059 := by exact prefixLift 3084059
  have htrace : WordTrace (prefixWord ++ tailWord_3084059) baseStart_3084059 baseEnd_3084059 := by
    simpa [prefixWord, tailWord_3084059, baseEnd_3084059] using wordTrace_append hprefix tailTrace_3084059
  have hstable : (prefixWord ++ tailWord_3084059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084059).length < 2 ^ (prefixWord ++ tailWord_3084059).sum := by decide
  have hdescent : baseEnd_3084059 < baseStart_3084059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084074 : List Nat := [3, 1, 4, 14]
def baseStart_3084074 : Nat := 118140960795 + 3084074 * 2 ^ 59
def prefixEnd_3084074 : Nat := 4983230072969 + 3 ^ 40 * 3084074 * 2
def baseEnd_3084074 : Nat := 1448205154123888230445

theorem tailTrace_3084074 : CollatzResearch.WordTrace tailWord_3084074 prefixEnd_3084074 1448205154123888230445 := by
  unfold tailWord_3084074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28121354957233522687538819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74990279885956060500103517 28121354957233522687538819)
  ·
    refine ⟨42182032435850284031308229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28121354957233522687538819 42182032435850284031308229)
    ·
      refine ⟨7909131081721928255870293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42182032435850284031308229 7909131081721928255870293)
      ·
        refine ⟨1448205154123888230445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7909131081721928255870293 1448205154123888230445)
        ·
          rfl

theorem cell22_3084074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 14].length) (baseStart_3084074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084074 prefixEnd_3084074 := by exact prefixLift 3084074
  have htrace : WordTrace (prefixWord ++ tailWord_3084074) baseStart_3084074 baseEnd_3084074 := by
    simpa [prefixWord, tailWord_3084074, baseEnd_3084074] using wordTrace_append hprefix tailTrace_3084074
  have hstable : (prefixWord ++ tailWord_3084074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084074).length < 2 ^ (prefixWord ++ tailWord_3084074).sum := by decide
  have hdescent : baseEnd_3084074 < baseStart_3084074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084076 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_3084076 : Nat := 118140960795 + 3084076 * 2 ^ 59
def prefixEnd_3084076 : Nat := 4983230072969 + 3 ^ 40 * 3084076 * 2
def baseEnd_3084076 : Nat := 1055742241997187181444399

theorem tailTrace_3084076 : CollatzResearch.WordTrace tailWord_3084076 prefixEnd_3084076 1055742241997187181444399 := by
  unfold tailWord_3084076
  simp only [CollatzResearch.WordTrace]
  refine ⟨56242746387463422545864041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74990328516617896727818721 56242746387463422545864041)
  ·
    refine ⟨42182059790597566909398031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56242746387463422545864041 42182059790597566909398031)
    ·
      refine ⟨63273089685896350364097047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42182059790597566909398031 63273089685896350364097047)
      ·
        refine ⟨94909634528844525546145571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63273089685896350364097047 94909634528844525546145571)
        ·
          refine ⟨142364451793266788319218357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94909634528844525546145571 142364451793266788319218357)
          ·
            refine ⟨13346667355618761404926721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142364451793266788319218357 13346667355618761404926721)
            ·
              refine ⟨10010000516714071053695041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13346667355618761404926721 10010000516714071053695041)
              ·
                refine ⟨7507500387535553290271281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10010000516714071053695041 7507500387535553290271281)
                ·
                  refine ⟨5630625290651664967703461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7507500387535553290271281 5630625290651664967703461)
                  ·
                    refine ⟨1055742241997187181444399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630625290651664967703461 1055742241997187181444399)
                    ·
                      rfl

theorem cell22_3084076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_3084076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084076 prefixEnd_3084076 := by exact prefixLift 3084076
  have htrace : WordTrace (prefixWord ++ tailWord_3084076) baseStart_3084076 baseEnd_3084076 := by
    simpa [prefixWord, tailWord_3084076, baseEnd_3084076] using wordTrace_append hprefix tailTrace_3084076
  have hstable : (prefixWord ++ tailWord_3084076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084076).length < 2 ^ (prefixWord ++ tailWord_3084076).sum := by decide
  have hdescent : baseEnd_3084076 < baseStart_3084076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084108 : List Nat := [2, 2, 1, 3, 4, 1, 3, 6]
def baseStart_3084108 : Nat := 118140960795 + 3084108 * 2 ^ 59
def prefixEnd_3084108 : Nat := 4983230072969 + 3 ^ 40 * 3084108 * 2
def baseEnd_3084108 : Nat := 117305910694572196071589

theorem tailTrace_3084108 : CollatzResearch.WordTrace tailWord_3084108 prefixEnd_3084108 117305910694572196071589 := by
  unfold tailWord_3084108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56243329955405457278446489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74991106607207276371261985 56243329955405457278446489)
  ·
    refine ⟨42182497466554092958834867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56243329955405457278446489 42182497466554092958834867)
    ·
      refine ⟨63273746199831139438252301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42182497466554092958834867 63273746199831139438252301)
      ·
        refine ⟨23727654824936677289344613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63273746199831139438252301 23727654824936677289344613)
        ·
          refine ⟨4448935279675626991752115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23727654824936677289344613 4448935279675626991752115)
          ·
            refine ⟨6673402919513440487628173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448935279675626991752115 6673402919513440487628173)
            ·
              refine ⟨2502526094817540182860565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6673402919513440487628173 2502526094817540182860565)
              ·
                refine ⟨117305910694572196071589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2502526094817540182860565 117305910694572196071589)
                ·
                  rfl

theorem cell22_3084108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_3084108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084108 prefixEnd_3084108 := by exact prefixLift 3084108
  have htrace : WordTrace (prefixWord ++ tailWord_3084108) baseStart_3084108 baseEnd_3084108 := by
    simpa [prefixWord, tailWord_3084108, baseEnd_3084108] using wordTrace_append hprefix tailTrace_3084108
  have hstable : (prefixWord ++ tailWord_3084108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084108).length < 2 ^ (prefixWord ++ tailWord_3084108).sum := by decide
  have hdescent : baseEnd_3084108 < baseStart_3084108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084136 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_3084136 : Nat := 118140960795 + 3084136 * 2 ^ 59
def prefixEnd_3084136 : Nat := 4983230072969 + 3 ^ 40 * 3084136 * 2
def baseEnd_3084136 : Nat := 351920927074455674981405

theorem tailTrace_3084136 : CollatzResearch.WordTrace tailWord_3084136 prefixEnd_3084136 351920927074455674981405 := by
  unfold tailWord_3084136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56243840577354737669456131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74991787436472983559274841 56243840577354737669456131)
  ·
    refine ⟨84365760866032106504184197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56243840577354737669456131 84365760866032106504184197)
    ·
      refine ⟨15818580162381019969534537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84365760866032106504184197 15818580162381019969534537)
      ·
        refine ⟨11863935121785764977150903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15818580162381019969534537 11863935121785764977150903)
        ·
          refine ⟨17795902682678647465726355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11863935121785764977150903 17795902682678647465726355)
          ·
            refine ⟨26693854024017971198589533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17795902682678647465726355 26693854024017971198589533)
            ·
              refine ⟨10010195259006739199471075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26693854024017971198589533 10010195259006739199471075)
              ·
                refine ⟨15015292888510108799206613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10010195259006739199471075 15015292888510108799206613)
                ·
                  refine ⟨351920927074455674981405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15015292888510108799206613 351920927074455674981405)
                  ·
                    rfl

theorem cell22_3084136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_3084136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084136 prefixEnd_3084136 := by exact prefixLift 3084136
  have htrace : WordTrace (prefixWord ++ tailWord_3084136) baseStart_3084136 baseEnd_3084136 := by
    simpa [prefixWord, tailWord_3084136, baseEnd_3084136] using wordTrace_append hprefix tailTrace_3084136
  have hstable : (prefixWord ++ tailWord_3084136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084136).length < 2 ^ (prefixWord ++ tailWord_3084136).sum := by decide
  have hdescent : baseEnd_3084136 < baseStart_3084136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084140 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_3084140 : Nat := 118140960795 + 3084140 * 2 ^ 59
def prefixEnd_3084140 : Nat := 4983230072969 + 3 ^ 40 * 3084140 * 2
def baseEnd_3084140 : Nat := 1055764150505112347844203

theorem tailTrace_3084140 : CollatzResearch.WordTrace tailWord_3084140 prefixEnd_3084140 1055764150505112347844203 := by
  unfold tailWord_3084140
  simp only [CollatzResearch.WordTrace]
  refine ⟨56243913523347492011028937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74991884697796656014705249 56243913523347492011028937)
  ·
    refine ⟨42182935142510619008271703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56243913523347492011028937 42182935142510619008271703)
    ·
      refine ⟨63274402713765928512407555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42182935142510619008271703 63274402713765928512407555)
      ·
        refine ⟨94911604070648892768611333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63274402713765928512407555 94911604070648892768611333)
        ·
          refine ⟨17795925763246667394114625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94911604070648892768611333 17795925763246667394114625)
          ·
            refine ⟨13346944322435000545585969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17795925763246667394114625 13346944322435000545585969)
            ·
              refine ⟨10010208241826250409189477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13346944322435000545585969 10010208241826250409189477)
              ·
                refine ⟨1876914045342421951723027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10010208241826250409189477 1876914045342421951723027)
                ·
                  refine ⟨2815371068013632927584541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876914045342421951723027 2815371068013632927584541)
                  ·
                    refine ⟨1055764150505112347844203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815371068013632927584541 1055764150505112347844203)
                    ·
                      rfl

theorem cell22_3084140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_3084140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084140 prefixEnd_3084140 := by exact prefixLift 3084140
  have htrace : WordTrace (prefixWord ++ tailWord_3084140) baseStart_3084140 baseEnd_3084140 := by
    simpa [prefixWord, tailWord_3084140, baseEnd_3084140] using wordTrace_append hprefix tailTrace_3084140
  have hstable : (prefixWord ++ tailWord_3084140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084140).length < 2 ^ (prefixWord ++ tailWord_3084140).sum := by decide
  have hdescent : baseEnd_3084140 < baseStart_3084140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084153 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 5]
def baseStart_3084153 : Nat := 118140960795 + 3084153 * 2 ^ 59
def prefixEnd_3084153 : Nat := 4983230072969 + 3 ^ 40 * 3084153 * 2
def baseEnd_3084153 : Nat := 351922866890261549089721

theorem tailTrace_3084153 : CollatzResearch.WordTrace tailWord_3084153 prefixEnd_3084153 351922866890261549089721 := by
  unfold tailWord_3084153
  simp only [CollatzResearch.WordTrace]
  refine ⟨112488301195647887242281113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74992200797098591494854075 112488301195647887242281113)
  ·
    refine ⟨84366225896735915431710835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112488301195647887242281113 84366225896735915431710835)
    ·
      refine ⟨126549338845103873147566253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84366225896735915431710835 126549338845103873147566253)
      ·
        refine ⟨47456002066913952430337345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126549338845103873147566253 47456002066913952430337345)
        ·
          refine ⟨35592001550185464322753009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47456002066913952430337345 35592001550185464322753009)
          ·
            refine ⟨26694001162639098242064757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35592001550185464322753009 26694001162639098242064757)
            ·
              refine ⟨2502562608997415460193571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26694001162639098242064757 2502562608997415460193571)
              ·
                refine ⟨3753843913496123190290357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502562608997415460193571 3753843913496123190290357)
                ·
                  refine ⟨351922866890261549089721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753843913496123190290357 351922866890261549089721)
                  ·
                    rfl

theorem cell22_3084153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_3084153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084153 prefixEnd_3084153 := by exact prefixLift 3084153
  have htrace : WordTrace (prefixWord ++ tailWord_3084153) baseStart_3084153 baseEnd_3084153 := by
    simpa [prefixWord, tailWord_3084153, baseEnd_3084153] using wordTrace_append hprefix tailTrace_3084153
  have hstable : (prefixWord ++ tailWord_3084153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084153).length < 2 ^ (prefixWord ++ tailWord_3084153).sum := by decide
  have hdescent : baseEnd_3084153 < baseStart_3084153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084183 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3084183 : Nat := 118140960795 + 3084183 * 2 ^ 59
def prefixEnd_3084183 : Nat := 4983230072969 + 3 ^ 40 * 3084183 * 2
def baseEnd_3084183 : Nat := 1055778870283874569019071

theorem tailTrace_3084183 : CollatzResearch.WordTrace tailWord_3084183 prefixEnd_3084183 1055778870283874569019071 := by
  unfold tailWord_3084183
  simp only [CollatzResearch.WordTrace]
  refine ⟨112489395385539202365873203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74992930257026134910582135 112489395385539202365873203)
  ·
    refine ⟨168734093078308803548809805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112489395385539202365873203 168734093078308803548809805)
    ·
      refine ⟨63275284904365801330803677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168734093078308803548809805 63275284904365801330803677)
      ·
        refine ⟨23728231839137175499051379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63275284904365801330803677 23728231839137175499051379)
        ·
          refine ⟨35592347758705763248577069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23728231839137175499051379 35592347758705763248577069)
          ·
            refine ⟨13347130409514661218216401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35592347758705763248577069 13347130409514661218216401)
            ·
              refine ⟨10010347807135995913662301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13347130409514661218216401 10010347807135995913662301)
              ·
                refine ⟨3753880427675998467623363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10010347807135995913662301 3753880427675998467623363)
                ·
                  refine ⟨5630820641513997701435045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753880427675998467623363 5630820641513997701435045)
                  ·
                    refine ⟨1055778870283874569019071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630820641513997701435045 1055778870283874569019071)
                    ·
                      rfl

theorem cell22_3084183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3084183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084183 prefixEnd_3084183 := by exact prefixLift 3084183
  have htrace : WordTrace (prefixWord ++ tailWord_3084183) baseStart_3084183 baseEnd_3084183 := by
    simpa [prefixWord, tailWord_3084183, baseEnd_3084183] using wordTrace_append hprefix tailTrace_3084183
  have hstable : (prefixWord ++ tailWord_3084183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084183).length < 2 ^ (prefixWord ++ tailWord_3084183).sum := by decide
  have hdescent : baseEnd_3084183 < baseStart_3084183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084211 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_3084211 : Nat := 118140960795 + 3084211 * 2 ^ 59
def prefixEnd_3084211 : Nat := 4983230072969 + 3 ^ 40 * 3084211 * 2
def baseEnd_3084211 : Nat := 1055788455256091829318985

theorem tailTrace_3084211 : CollatzResearch.WordTrace tailWord_3084211 prefixEnd_3084211 1055788455256091829318985 := by
  unfold tailWord_3084211
  simp only [CollatzResearch.WordTrace]
  refine ⟨112490416629437763147892487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74993611086291842098594991 112490416629437763147892487)
  ·
    refine ⟨168735624944156644721838731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112490416629437763147892487 168735624944156644721838731)
    ·
      refine ⟨253103437416234967082758097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168735624944156644721838731 253103437416234967082758097)
      ·
        refine ⟨189827578062176225312068573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253103437416234967082758097 189827578062176225312068573)
        ·
          refine ⟨71185341773316084492025715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189827578062176225312068573 71185341773316084492025715)
          ·
            refine ⟨106778012659974126738038573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71185341773316084492025715 106778012659974126738038573)
            ·
              refine ⟨40041754747490297526764465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106778012659974126738038573 40041754747490297526764465)
              ·
                refine ⟨30031316060617723145073349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40041754747490297526764465 30031316060617723145073349)
                ·
                  refine ⟨5630871761365823089701253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30031316060617723145073349 5630871761365823089701253)
                  ·
                    refine ⟨1055788455256091829318985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630871761365823089701253 1055788455256091829318985)
                    ·
                      rfl

theorem cell22_3084211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_3084211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084211 prefixEnd_3084211 := by exact prefixLift 3084211
  have htrace : WordTrace (prefixWord ++ tailWord_3084211) baseStart_3084211 baseEnd_3084211 := by
    simpa [prefixWord, tailWord_3084211, baseEnd_3084211] using wordTrace_append hprefix tailTrace_3084211
  have hstable : (prefixWord ++ tailWord_3084211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084211).length < 2 ^ (prefixWord ++ tailWord_3084211).sum := by decide
  have hdescent : baseEnd_3084211 < baseStart_3084211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084249 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 4]
def baseStart_3084249 : Nat := 118140960795 + 3084249 * 2 ^ 59
def prefixEnd_3084249 : Nat := 4983230072969 + 3 ^ 40 * 3084249 * 2
def baseEnd_3084249 : Nat := 351933821144224132289623

theorem tailTrace_3084249 : CollatzResearch.WordTrace tailWord_3084249 prefixEnd_3084249 351933821144224132289623 := by
  unfold tailWord_3084249
  simp only [CollatzResearch.WordTrace]
  refine ⟨112491802603300095637775801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74994535068866730425183867 112491802603300095637775801)
  ·
    refine ⟨84368851952475071728331851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112491802603300095637775801 84368851952475071728331851)
    ·
      refine ⟨126553277928712607592497777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84368851952475071728331851 126553277928712607592497777)
      ·
        refine ⟨94914958446534455694373333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126553277928712607592497777 94914958446534455694373333)
        ·
          refine ⟨2224569338590651305336875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94914958446534455694373333 2224569338590651305336875)
          ·
            refine ⟨3336854007885976958005313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224569338590651305336875 3336854007885976958005313)
            ·
              refine ⟨2502640505914482718503985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336854007885976958005313 2502640505914482718503985)
              ·
                refine ⟨1876980379435862038877989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502640505914482718503985 1876980379435862038877989)
                ·
                  refine ⟨351933821144224132289623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876980379435862038877989 351933821144224132289623)
                  ·
                    rfl

theorem cell22_3084249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_3084249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084249 prefixEnd_3084249 := by exact prefixLift 3084249
  have htrace : WordTrace (prefixWord ++ tailWord_3084249) baseStart_3084249 baseEnd_3084249 := by
    simpa [prefixWord, tailWord_3084249, baseEnd_3084249] using wordTrace_append hprefix tailTrace_3084249
  have hstable : (prefixWord ++ tailWord_3084249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084249).length < 2 ^ (prefixWord ++ tailWord_3084249).sum := by decide
  have hdescent : baseEnd_3084249 < baseStart_3084249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084294 : List Nat := [6, 2, 1, 2, 1, 1, 9]
def baseStart_3084294 : Nat := 118140960795 + 3084294 * 2 ^ 59
def prefixEnd_3084294 : Nat := 4983230072969 + 3 ^ 40 * 3084294 * 2
def baseEnd_3084294 : Nat := 39104328438974343684953

theorem tailTrace_3084294 : CollatzResearch.WordTrace tailWord_3084294 prefixEnd_3084294 39104328438974343684953 := by
  unfold tailWord_3084294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515420121504283385098873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74995629258758045548775957 3515420121504283385098873)
  ·
    refine ⟨2636565091128212538824155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515420121504283385098873 2636565091128212538824155)
    ·
      refine ⟨3954847636692318808236233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636565091128212538824155 3954847636692318808236233)
      ·
        refine ⟨2966135727519239106177175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3954847636692318808236233 2966135727519239106177175)
        ·
          refine ⟨4449203591278858659265763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966135727519239106177175 4449203591278858659265763)
          ·
            refine ⟨6673805386918287988898645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449203591278858659265763 6673805386918287988898645)
            ·
              refine ⟨39104328438974343684953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6673805386918287988898645 39104328438974343684953)
              ·
                rfl

theorem cell22_3084294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 9].length) (baseStart_3084294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084294 prefixEnd_3084294 := by exact prefixLift 3084294
  have htrace : WordTrace (prefixWord ++ tailWord_3084294) baseStart_3084294 baseEnd_3084294 := by
    simpa [prefixWord, tailWord_3084294, baseEnd_3084294] using wordTrace_append hprefix tailTrace_3084294
  have hstable : (prefixWord ++ tailWord_3084294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084294).length < 2 ^ (prefixWord ++ tailWord_3084294).sum := by decide
  have hdescent : baseEnd_3084294 < baseStart_3084294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084348 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_3084348 : Nat := 118140960795 + 3084348 * 2 ^ 59
def prefixEnd_3084348 : Nat := 4983230072969 + 3 ^ 40 * 3084348 * 2
def baseEnd_3084348 : Nat := 1055835353155869138643565

theorem tailTrace_3084348 : CollatzResearch.WordTrace tailWord_3084348 prefixEnd_3084348 1055835353155869138643565 := by
  unfold tailWord_3084348
  simp only [CollatzResearch.WordTrace]
  refine ⟨56247706714970717772814849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74996942286627623697086465 56247706714970717772814849)
  ·
    refine ⟨42185780036228038329611137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56247706714970717772814849 42185780036228038329611137)
    ·
      refine ⟨31639335027171028747208353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42185780036228038329611137 31639335027171028747208353)
      ·
        refine ⟨23729501270378271560406265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31639335027171028747208353 23729501270378271560406265)
        ·
          refine ⟨17797125952783703670304699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23729501270378271560406265 17797125952783703670304699)
          ·
            refine ⟨26695688929175555505457049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17797125952783703670304699 26695688929175555505457049)
            ·
              refine ⟨20021766696881666629092787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26695688929175555505457049 20021766696881666629092787)
              ·
                refine ⟨30032650045322499943639181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20021766696881666629092787 30032650045322499943639181)
                ·
                  refine ⟨11262243766995937478864693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30032650045322499943639181 11262243766995937478864693)
                  ·
                    refine ⟨1055835353155869138643565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11262243766995937478864693 1055835353155869138643565)
                    ·
                      rfl

theorem cell22_3084348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_3084348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084348 prefixEnd_3084348 := by exact prefixLift 3084348
  have htrace : WordTrace (prefixWord ++ tailWord_3084348) baseStart_3084348 baseEnd_3084348 := by
    simpa [prefixWord, tailWord_3084348, baseEnd_3084348] using wordTrace_append hprefix tailTrace_3084348
  have hstable : (prefixWord ++ tailWord_3084348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084348).length < 2 ^ (prefixWord ++ tailWord_3084348).sum := by decide
  have hdescent : baseEnd_3084348 < baseStart_3084348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084363 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_3084363 : Nat := 118140960795 + 3084363 * 2 ^ 59
def prefixEnd_3084363 : Nat := 4983230072969 + 3 ^ 40 * 3084363 * 2
def baseEnd_3084363 : Nat := 1055840487962414099518519

theorem tailTrace_3084363 : CollatzResearch.WordTrace tailWord_3084363 prefixEnd_3084363 1055840487962414099518519 := by
  unfold tailWord_3084363
  simp only [CollatzResearch.WordTrace]
  refine ⟨112495960524887093107425743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74997307016591395404950495 112495960524887093107425743)
  ·
    refine ⟨168743940787330639661138615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112495960524887093107425743 168743940787330639661138615)
    ·
      refine ⟨253115911180995959491707923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168743940787330639661138615 253115911180995959491707923)
      ·
        refine ⟨379673866771493939237561885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253115911180995959491707923 379673866771493939237561885)
        ·
          refine ⟨142377700039310227214085707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379673866771493939237561885 142377700039310227214085707)
          ·
            refine ⟨213566550058965340821128561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142377700039310227214085707 213566550058965340821128561)
            ·
              refine ⟨160174912544224005615846421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213566550058965340821128561 160174912544224005615846421)
              ·
                refine ⟨7508199025510500263242801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160174912544224005615846421 7508199025510500263242801)
                ·
                  refine ⟨5631149269132875197432101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508199025510500263242801 5631149269132875197432101)
                  ·
                    refine ⟨1055840487962414099518519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631149269132875197432101 1055840487962414099518519)
                    ·
                      rfl

theorem cell22_3084363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_3084363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084363 prefixEnd_3084363 := by exact prefixLift 3084363
  have htrace : WordTrace (prefixWord ++ tailWord_3084363) baseStart_3084363 baseEnd_3084363 := by
    simpa [prefixWord, tailWord_3084363, baseEnd_3084363] using wordTrace_append hprefix tailTrace_3084363
  have hstable : (prefixWord ++ tailWord_3084363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084363).length < 2 ^ (prefixWord ++ tailWord_3084363).sum := by decide
  have hdescent : baseEnd_3084363 < baseStart_3084363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084378 : List Nat := [3, 1, 1, 2, 1, 1, 6, 7]
def baseStart_3084378 : Nat := 118140960795 + 3084378 * 2 ^ 59
def prefixEnd_3084378 : Nat := 4983230072969 + 3 ^ 40 * 3084378 * 2
def baseEnd_3084378 : Nat := 117316180307662117821497

theorem tailTrace_3084378 : CollatzResearch.WordTrace tailWord_3084378 prefixEnd_3084378 117316180307662117821497 := by
  unfold tailWord_3084378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28124126904958187667305447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74997671746555167112814525 28124126904958187667305447)
  ·
    refine ⟨42186190357437281500958171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28124126904958187667305447 42186190357437281500958171)
    ·
      refine ⟨63279285536155922251437257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42186190357437281500958171 63279285536155922251437257)
      ·
        refine ⟨47459464152116941688577943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63279285536155922251437257 47459464152116941688577943)
        ·
          refine ⟨71189196228175412532866915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47459464152116941688577943 71189196228175412532866915)
          ·
            refine ⟨106783794342263118799300373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71189196228175412532866915 106783794342263118799300373)
            ·
              refine ⟨5005490359793583693717205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106783794342263118799300373 5005490359793583693717205)
              ·
                refine ⟨117316180307662117821497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5005490359793583693717205 117316180307662117821497)
                ·
                  rfl

theorem cell22_3084378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_3084378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084378 prefixEnd_3084378 := by exact prefixLift 3084378
  have htrace : WordTrace (prefixWord ++ tailWord_3084378) baseStart_3084378 baseEnd_3084378 := by
    simpa [prefixWord, tailWord_3084378, baseEnd_3084378] using wordTrace_append hprefix tailTrace_3084378
  have hstable : (prefixWord ++ tailWord_3084378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084378).length < 2 ^ (prefixWord ++ tailWord_3084378).sum := by decide
  have hdescent : baseEnd_3084378 < baseStart_3084378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084386 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3084386 : Nat := 118140960795 + 3084386 * 2 ^ 59
def prefixEnd_3084386 : Nat := 4983230072969 + 3 ^ 40 * 3084386 * 2
def baseEnd_3084386 : Nat := 1055848361332449706193449

theorem tailTrace_3084386 : CollatzResearch.WordTrace tailWord_3084386 prefixEnd_3084386 1055848361332449706193449 := by
  unfold tailWord_3084386
  simp only [CollatzResearch.WordTrace]
  refine ⟨28124199850950942008878253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74997866269202512023675341 28124199850950942008878253)
  ·
    refine ⟨10546574944106603253329345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28124199850950942008878253 10546574944106603253329345)
    ·
      refine ⟨7909931208079952439997009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10546574944106603253329345 7909931208079952439997009)
      ·
        refine ⟨5932448406059964329997757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7909931208079952439997009 5932448406059964329997757)
        ·
          refine ⟨2224668152272486623749159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5932448406059964329997757 2224668152272486623749159)
          ·
            refine ⟨3337002228408729935623739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224668152272486623749159 3337002228408729935623739)
            ·
              refine ⟨5005503342613094903435609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337002228408729935623739 5005503342613094903435609)
              ·
                refine ⟨3754127506959821177576707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5005503342613094903435609 3754127506959821177576707)
                ·
                  refine ⟨5631191260439731766365061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754127506959821177576707 5631191260439731766365061)
                  ·
                    refine ⟨1055848361332449706193449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631191260439731766365061 1055848361332449706193449)
                    ·
                      rfl

theorem cell22_3084386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3084386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084386 prefixEnd_3084386 := by exact prefixLift 3084386
  have htrace : WordTrace (prefixWord ++ tailWord_3084386) baseStart_3084386 baseEnd_3084386 := by
    simpa [prefixWord, tailWord_3084386, baseEnd_3084386] using wordTrace_append hprefix tailTrace_3084386
  have hstable : (prefixWord ++ tailWord_3084386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084386).length < 2 ^ (prefixWord ++ tailWord_3084386).sum := by decide
  have hdescent : baseEnd_3084386 < baseStart_3084386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084423 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 7]
def baseStart_3084423 : Nat := 118140960795 + 3084423 * 2 ^ 59
def prefixEnd_3084423 : Nat := 4983230072969 + 3 ^ 40 * 3084423 * 2
def baseEnd_3084423 : Nat := 351953675729531314339445

theorem tailTrace_3084423 : CollatzResearch.WordTrace tailWord_3084423 prefixEnd_3084423 351953675729531314339445 := by
  unfold tailWord_3084423
  simp only [CollatzResearch.WordTrace]
  refine ⟨112498148904669723354609923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74998765936446482236406615 112498148904669723354609923)
  ·
    refine ⟨168747223357004585031914885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112498148904669723354609923 168747223357004585031914885)
    ·
      refine ⟨31640104379438359693484041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168747223357004585031914885 31640104379438359693484041)
      ·
        refine ⟨23730078284578769770113031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31640104379438359693484041 23730078284578769770113031)
        ·
          refine ⟨35595117426868154655169547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23730078284578769770113031 35595117426868154655169547)
          ·
            refine ⟨53392676140302231982754321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35595117426868154655169547 53392676140302231982754321)
            ·
              refine ⟨40044507105226673987065741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53392676140302231982754321 40044507105226673987065741)
              ·
                refine ⟨15016690164460002745149653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40044507105226673987065741 15016690164460002745149653)
                ·
                  refine ⟨351953675729531314339445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15016690164460002745149653 351953675729531314339445)
                  ·
                    rfl

theorem cell22_3084423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_3084423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084423 prefixEnd_3084423 := by exact prefixLift 3084423
  have htrace : WordTrace (prefixWord ++ tailWord_3084423) baseStart_3084423 baseEnd_3084423 := by
    simpa [prefixWord, tailWord_3084423, baseEnd_3084423] using wordTrace_append hprefix tailTrace_3084423
  have hstable : (prefixWord ++ tailWord_3084423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084423).length < 2 ^ (prefixWord ++ tailWord_3084423).sum := by decide
  have hdescent : baseEnd_3084423 < baseStart_3084423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084461 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3084461 : Nat := 118140960795 + 3084461 * 2 ^ 59
def prefixEnd_3084461 : Nat := 4983230072969 + 3 ^ 40 * 3084461 * 2
def baseEnd_3084461 : Nat := 1055874035365174510568219

theorem tailTrace_3084461 : CollatzResearch.WordTrace tailWord_3084461 prefixEnd_3084461 1055874035365174510568219 := by
  unfold tailWord_3084461
  simp only [CollatzResearch.WordTrace]
  refine ⟨112499534878532055844493237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74999689919021370562995491 112499534878532055844493237)
  ·
    refine ⟨10546831394862380235421241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112499534878532055844493237 10546831394862380235421241)
    ·
      refine ⟨7910123546146785176565931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10546831394862380235421241 7910123546146785176565931)
      ·
        refine ⟨11865185319220177764848897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910123546146785176565931 11865185319220177764848897)
        ·
          refine ⟨8898888989415133323636673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865185319220177764848897 8898888989415133323636673)
          ·
            refine ⟨6674166742061349992727505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8898888989415133323636673 6674166742061349992727505)
            ·
              refine ⟨5005625056546012494545629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6674166742061349992727505 5005625056546012494545629)
              ·
                refine ⟨1877109396204754685454611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5005625056546012494545629 1877109396204754685454611)
                ·
                  refine ⟨2815664094307132028181917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877109396204754685454611 2815664094307132028181917)
                  ·
                    refine ⟨1055874035365174510568219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815664094307132028181917 1055874035365174510568219)
                    ·
                      rfl

theorem cell22_3084461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3084461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084461 prefixEnd_3084461 := by exact prefixLift 3084461
  have htrace : WordTrace (prefixWord ++ tailWord_3084461) baseStart_3084461 baseEnd_3084461 := by
    simpa [prefixWord, tailWord_3084461, baseEnd_3084461] using wordTrace_append hprefix tailTrace_3084461
  have hstable : (prefixWord ++ tailWord_3084461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084461).length < 2 ^ (prefixWord ++ tailWord_3084461).sum := by decide
  have hdescent : baseEnd_3084461 < baseStart_3084461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084517 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_3084517 : Nat := 118140960795 + 3084517 * 2 ^ 59
def prefixEnd_3084517 : Nat := 4983230072969 + 3 ^ 40 * 3084517 * 2
def baseEnd_3084517 : Nat := 1055893205309609031168047

theorem tailTrace_3084517 : CollatzResearch.WordTrace tailWord_3084517 prefixEnd_3084517 1055893205309609031168047 := by
  unfold tailWord_3084517
  simp only [CollatzResearch.WordTrace]
  refine ⟨112501577366329177408531805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75001051577552784939021203 112501577366329177408531805)
  ·
    refine ⟨42188091512373441528199427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112501577366329177408531805 42188091512373441528199427)
    ·
      refine ⟨63282137268560162292299141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42188091512373441528199427 63282137268560162292299141)
      ·
        refine ⟨11865400737855030429806089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63282137268560162292299141 11865400737855030429806089)
        ·
          refine ⟨8899050553391272822354567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865400737855030429806089 8899050553391272822354567)
          ·
            refine ⟨13348575830086909233531851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8899050553391272822354567 13348575830086909233531851)
            ·
              refine ⟨20022863745130363850297777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13348575830086909233531851 20022863745130363850297777)
              ·
                refine ⟨15017147808847772887723333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20022863745130363850297777 15017147808847772887723333)
                ·
                  refine ⟨2815715214158957416448125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15017147808847772887723333 2815715214158957416448125)
                  ·
                    refine ⟨1055893205309609031168047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815715214158957416448125 1055893205309609031168047)
                    ·
                      rfl

theorem cell22_3084517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_3084517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084517 prefixEnd_3084517 := by exact prefixLift 3084517
  have htrace : WordTrace (prefixWord ++ tailWord_3084517) baseStart_3084517 baseEnd_3084517 := by
    simpa [prefixWord, tailWord_3084517, baseEnd_3084517] using wordTrace_append hprefix tailTrace_3084517
  have hstable : (prefixWord ++ tailWord_3084517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084517).length < 2 ^ (prefixWord ++ tailWord_3084517).sum := by decide
  have hdescent : baseEnd_3084517 < baseStart_3084517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084519 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 4]
def baseStart_3084519 : Nat := 118140960795 + 3084519 * 2 ^ 59
def prefixEnd_3084519 : Nat := 4983230072969 + 3 ^ 40 * 3084519 * 2
def baseEnd_3084519 : Nat := 351964629983493897539347

theorem tailTrace_3084519 : CollatzResearch.WordTrace tailWord_3084519 prefixEnd_3084519 351964629983493897539347 := by
  unfold tailWord_3084519
  simp only [CollatzResearch.WordTrace]
  refine ⟨112501650312321931750104611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75001100208214621166736407 112501650312321931750104611)
  ·
    refine ⟨168752475468482897625156917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112501650312321931750104611 168752475468482897625156917)
    ·
      refine ⟨15820544575170271652358461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168752475468482897625156917 15820544575170271652358461)
      ·
        refine ⟨5932704215688851869634423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15820544575170271652358461 5932704215688851869634423)
        ·
          refine ⟨8899056323533277804451635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5932704215688851869634423 8899056323533277804451635)
          ·
            refine ⟨13348584485299916706677453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8899056323533277804451635 13348584485299916706677453)
            ·
              refine ⟨5005719181987468765004045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13348584485299916706677453 5005719181987468765004045)
              ·
                refine ⟨1877144693245300786876517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5005719181987468765004045 1877144693245300786876517)
                ·
                  refine ⟨351964629983493897539347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877144693245300786876517 351964629983493897539347)
                  ·
                    rfl

theorem cell22_3084519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 4].length) (baseStart_3084519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084519 prefixEnd_3084519 := by exact prefixLift 3084519
  have htrace : WordTrace (prefixWord ++ tailWord_3084519) baseStart_3084519 baseEnd_3084519 := by
    simpa [prefixWord, tailWord_3084519, baseEnd_3084519] using wordTrace_append hprefix tailTrace_3084519
  have hstable : (prefixWord ++ tailWord_3084519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084519).length < 2 ^ (prefixWord ++ tailWord_3084519).sum := by decide
  have hdescent : baseEnd_3084519 < baseStart_3084519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084530 : List Nat := [3, 2, 1, 3, 2, 1, 10]
def baseStart_3084530 : Nat := 118140960795 + 3084530 * 2 ^ 59
def prefixEnd_3084530 : Nat := 4983230072969 + 3 ^ 40 * 3084530 * 2
def baseEnd_3084530 : Nat := 39107320573158567799741

theorem tailTrace_3084530 : CollatzResearch.WordTrace tailWord_3084530 prefixEnd_3084530 39107320573158567799741 := by
  unfold tailWord_3084530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28125512878820520157188761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75001367676854720419170029 28125512878820520157188761)
  ·
    refine ⟨21094134659115390117891571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28125512878820520157188761 21094134659115390117891571)
    ·
      refine ⟨31641201988673085176837357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21094134659115390117891571 31641201988673085176837357)
      ·
        refine ⟨11865450745752406941314009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31641201988673085176837357 11865450745752406941314009)
        ·
          refine ⟨8899088059314305205985507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865450745752406941314009 8899088059314305205985507)
          ·
            refine ⟨13348632088971457808978261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8899088059314305205985507 13348632088971457808978261)
            ·
              refine ⟨39107320573158567799741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13348632088971457808978261 39107320573158567799741)
              ·
                rfl

theorem cell22_3084530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 10].length) (baseStart_3084530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084530 prefixEnd_3084530 := by exact prefixLift 3084530
  have htrace : WordTrace (prefixWord ++ tailWord_3084530) baseStart_3084530 baseEnd_3084530 := by
    simpa [prefixWord, tailWord_3084530, baseEnd_3084530] using wordTrace_append hprefix tailTrace_3084530
  have hstable : (prefixWord ++ tailWord_3084530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084530).length < 2 ^ (prefixWord ++ tailWord_3084530).sum := by decide
  have hdescent : baseEnd_3084530 < baseStart_3084530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084551 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3084551 : Nat := 118140960795 + 3084551 * 2 ^ 59
def prefixEnd_3084551 : Nat := 4983230072969 + 3 ^ 40 * 3084551 * 2
def baseEnd_3084551 : Nat := 1055904844204444275817943

theorem tailTrace_3084551 : CollatzResearch.WordTrace tailWord_3084551 prefixEnd_3084551 1055904844204444275817943 := by
  unfold tailWord_3084551
  simp only [CollatzResearch.WordTrace]
  refine ⟨112502817448206001215269507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75001878298804000810179671 112502817448206001215269507)
  ·
    refine ⟨168754226172309001822904261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112502817448206001215269507 168754226172309001822904261)
    ·
      refine ⟨31641417407307937841794549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168754226172309001822904261 31641417407307937841794549)
      ·
        refine ⟨2966382881935119172668239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31641417407307937841794549 2966382881935119172668239)
        ·
          refine ⟨4449574322902678759002359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966382881935119172668239 4449574322902678759002359)
          ·
            refine ⟨6674361484354018138503539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449574322902678759002359 6674361484354018138503539)
            ·
              refine ⟨10011542226531027207755309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674361484354018138503539 10011542226531027207755309)
              ·
                refine ⟨3754328334949135202908241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10011542226531027207755309 3754328334949135202908241)
                ·
                  refine ⟨2815746251211851402181181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754328334949135202908241 2815746251211851402181181)
                  ·
                    refine ⟨1055904844204444275817943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815746251211851402181181 1055904844204444275817943)
                    ·
                      rfl

theorem cell22_3084551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3084551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084551 prefixEnd_3084551 := by exact prefixLift 3084551
  have htrace : WordTrace (prefixWord ++ tailWord_3084551) baseStart_3084551 baseEnd_3084551 := by
    simpa [prefixWord, tailWord_3084551, baseEnd_3084551] using wordTrace_append hprefix tailTrace_3084551
  have hstable : (prefixWord ++ tailWord_3084551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084551).length < 2 ^ (prefixWord ++ tailWord_3084551).sum := by decide
  have hdescent : baseEnd_3084551 < baseStart_3084551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084579 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 1, 3]
def baseStart_3084579 : Nat := 118140960795 + 3084579 * 2 ^ 59
def prefixEnd_3084579 : Nat := 4983230072969 + 3 ^ 40 * 3084579 * 2
def baseEnd_3084579 : Nat := 1055914429176661536117857

theorem tailTrace_3084579 : CollatzResearch.WordTrace tailWord_3084579 prefixEnd_3084579 1055914429176661536117857 := by
  unfold tailWord_3084579
  simp only [CollatzResearch.WordTrace]
  refine ⟨112503838692104561997288791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75002559128069707998192527 112503838692104561997288791)
  ·
    refine ⟨168755758038156842995933187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112503838692104561997288791 168755758038156842995933187)
    ·
      refine ⟨253133637057235264493899781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168755758038156842995933187 253133637057235264493899781)
      ·
        refine ⟨47462556948231612092606209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253133637057235264493899781 47462556948231612092606209)
        ·
          refine ⟨35596917711173709069454657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47462556948231612092606209 35596917711173709069454657)
          ·
            refine ⟨26697688283380281802090993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35596917711173709069454657 26697688283380281802090993)
            ·
              refine ⟨20023266212535211351568245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26697688283380281802090993 20023266212535211351568245)
              ·
                refine ⟨1877181207425176064209523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20023266212535211351568245 1877181207425176064209523)
                ·
                  refine ⟨2815771811137764096314285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877181207425176064209523 2815771811137764096314285)
                  ·
                    refine ⟨1055914429176661536117857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2815771811137764096314285 1055914429176661536117857)
                    ·
                      rfl

theorem cell22_3084579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 3].length) (baseStart_3084579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084579 prefixEnd_3084579 := by exact prefixLift 3084579
  have htrace : WordTrace (prefixWord ++ tailWord_3084579) baseStart_3084579 baseEnd_3084579 := by
    simpa [prefixWord, tailWord_3084579, baseEnd_3084579] using wordTrace_append hprefix tailTrace_3084579
  have hstable : (prefixWord ++ tailWord_3084579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084579).length < 2 ^ (prefixWord ++ tailWord_3084579).sum := by decide
  have hdescent : baseEnd_3084579 < baseStart_3084579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084639 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 1, 4]
def baseStart_3084639 : Nat := 118140960795 + 3084639 * 2 ^ 59
def prefixEnd_3084639 : Nat := 4983230072969 + 3 ^ 40 * 3084639 * 2
def baseEnd_3084639 : Nat := 1055934968402841379617673

theorem tailTrace_3084639 : CollatzResearch.WordTrace tailWord_3084639 prefixEnd_3084639 1055934968402841379617673 := by
  unfold tailWord_3084639
  simp only [CollatzResearch.WordTrace]
  refine ⟨112506027071887192244472971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75004018047924794829648647 112506027071887192244472971)
  ·
    refine ⟨168759040607830788366709457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112506027071887192244472971 168759040607830788366709457)
    ·
      refine ⟨126569280455873091275032093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168759040607830788366709457 126569280455873091275032093)
      ·
        refine ⟨47463480170952409228137035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126569280455873091275032093 47463480170952409228137035)
        ·
          refine ⟨71195220256428613842205553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47463480170952409228137035 71195220256428613842205553)
          ·
            refine ⟨53396415192321460381654165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71195220256428613842205553 53396415192321460381654165)
            ·
              refine ⟨2502956962140068455390039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53396415192321460381654165 2502956962140068455390039)
              ·
                refine ⟨3754435443210102683085059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502956962140068455390039 3754435443210102683085059)
                ·
                  refine ⟨5631653164815154024627589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754435443210102683085059 5631653164815154024627589)
                  ·
                    refine ⟨1055934968402841379617673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631653164815154024627589 1055934968402841379617673)
                    ·
                      rfl

theorem cell22_3084639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_3084639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084639 prefixEnd_3084639 := by exact prefixLift 3084639
  have htrace : WordTrace (prefixWord ++ tailWord_3084639) baseStart_3084639 baseEnd_3084639 := by
    simpa [prefixWord, tailWord_3084639, baseEnd_3084639] using wordTrace_append hprefix tailTrace_3084639
  have hstable : (prefixWord ++ tailWord_3084639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084639).length < 2 ^ (prefixWord ++ tailWord_3084639).sum := by decide
  have hdescent : baseEnd_3084639 < baseStart_3084639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084665 : List Nat := [1, 2, 1, 3, 2, 1, 1, 11]
def baseStart_3084665 : Nat := 118140960795 + 3084665 * 2 ^ 59
def prefixEnd_3084665 : Nat := 4983230072969 + 3 ^ 40 * 3084665 * 2
def baseEnd_3084665 : Nat := 117327096526020664274177

theorem tailTrace_3084665 : CollatzResearch.WordTrace tailWord_3084665 prefixEnd_3084665 117327096526020664274177 := by
  unfold tailWord_3084665
  simp only [CollatzResearch.WordTrace]
  refine ⟨112506975369792998684919449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75004650246528665789946299 112506975369792998684919449)
  ·
    refine ⟨84380231527344749013689587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112506975369792998684919449 84380231527344749013689587)
    ·
      refine ⟨126570347291017123520534381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84380231527344749013689587 126570347291017123520534381)
      ·
        refine ⟨47463880234131421320200393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126570347291017123520534381 47463880234131421320200393)
        ·
          refine ⟨35597910175598565990150295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47463880234131421320200393 35597910175598565990150295)
          ·
            refine ⟨53396865263397848985225443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35597910175598565990150295 53396865263397848985225443)
            ·
              refine ⟨80095297895096773477838165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53396865263397848985225443 80095297895096773477838165)
              ·
                refine ⟨117327096526020664274177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80095297895096773477838165 117327096526020664274177)
                ·
                  rfl

theorem cell22_3084665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 11].length) (baseStart_3084665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084665 prefixEnd_3084665 := by exact prefixLift 3084665
  have htrace : WordTrace (prefixWord ++ tailWord_3084665) baseStart_3084665 baseEnd_3084665 := by
    simpa [prefixWord, tailWord_3084665, baseEnd_3084665] using wordTrace_append hprefix tailTrace_3084665
  have hstable : (prefixWord ++ tailWord_3084665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084665).length < 2 ^ (prefixWord ++ tailWord_3084665).sum := by decide
  have hdescent : baseEnd_3084665 < baseStart_3084665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084669 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_3084669 : Nat := 118140960795 + 3084669 * 2 ^ 59
def prefixEnd_3084669 : Nat := 4983230072969 + 3 ^ 40 * 3084669 * 2
def baseEnd_3084669 : Nat := 1055945238015931301367581

theorem tailTrace_3084669 : CollatzResearch.WordTrace tailWord_3084669 prefixEnd_3084669 1055945238015931301367581 := by
  unfold tailWord_3084669
  simp only [CollatzResearch.WordTrace]
  refine ⟨112507121261778507368065061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75004747507852338245376707 112507121261778507368065061)
  ·
    refine ⟨21095085236583470131512199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112507121261778507368065061 21095085236583470131512199)
    ·
      refine ⟨31642627854875205197268299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21095085236583470131512199 31642627854875205197268299)
      ·
        refine ⟨47463941782312807795902449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31642627854875205197268299 47463941782312807795902449)
        ·
          refine ⟨35597956336734605846926837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47463941782312807795902449 35597956336734605846926837)
          ·
            refine ⟨3337308406568869298149391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35597956336734605846926837 3337308406568869298149391)
            ·
              refine ⟨5005962609853303947224087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337308406568869298149391 5005962609853303947224087)
              ·
                refine ⟨7508943914779955920836131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005962609853303947224087 7508943914779955920836131)
                ·
                  refine ⟨11263415872169933881254197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7508943914779955920836131 11263415872169933881254197)
                  ·
                    refine ⟨1055945238015931301367581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11263415872169933881254197 1055945238015931301367581)
                    ·
                      rfl

theorem cell22_3084669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_3084669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084669 prefixEnd_3084669 := by exact prefixLift 3084669
  have htrace : WordTrace (prefixWord ++ tailWord_3084669) baseStart_3084669 baseEnd_3084669 := by
    simpa [prefixWord, tailWord_3084669, baseEnd_3084669] using wordTrace_append hprefix tailTrace_3084669
  have hstable : (prefixWord ++ tailWord_3084669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084669).length < 2 ^ (prefixWord ++ tailWord_3084669).sum := by decide
  have hdescent : baseEnd_3084669 < baseStart_3084669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084896 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_3084896 : Nat := 118140960795 + 3084896 * 2 ^ 59
def prefixEnd_3084896 : Nat := 4983230072969 + 3 ^ 40 * 3084896 * 2
def baseEnd_3084896 : Nat := 352007648251659458647295

theorem tailTrace_3084896 : CollatzResearch.WordTrace tailWord_3084896 prefixEnd_3084896 352007648251659458647295 := by
  unfold tailWord_3084896
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257700315978062568289271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75010267087970750091052361 56257700315978062568289271)
  ·
    refine ⟨84386550473967093852433907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56257700315978062568289271 84386550473967093852433907)
    ·
      refine ⟨126579825710950640778650861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84386550473967093852433907 126579825710950640778650861)
      ·
        refine ⟨47467434641606490291994073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126579825710950640778650861 47467434641606490291994073)
        ·
          refine ⟨35600575981204867718995555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47467434641606490291994073 35600575981204867718995555)
          ·
            refine ⟨53400863971807301578493333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35600575981204867718995555 53400863971807301578493333)
            ·
              refine ⟨2503165498678467261491875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53400863971807301578493333 2503165498678467261491875)
              ·
                refine ⟨3754748248017700892237813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503165498678467261491875 3754748248017700892237813)
                ·
                  refine ⟨352007648251659458647295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3754748248017700892237813 352007648251659458647295)
                  ·
                    rfl

theorem cell22_3084896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_3084896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084896 prefixEnd_3084896 := by exact prefixLift 3084896
  have htrace : WordTrace (prefixWord ++ tailWord_3084896) baseStart_3084896 baseEnd_3084896 := by
    simpa [prefixWord, tailWord_3084896, baseEnd_3084896] using wordTrace_append hprefix tailTrace_3084896
  have hstable : (prefixWord ++ tailWord_3084896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084896).length < 2 ^ (prefixWord ++ tailWord_3084896).sum := by decide
  have hdescent : baseEnd_3084896 < baseStart_3084896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084956 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3084956 : Nat := 118140960795 + 3084956 * 2 ^ 59
def prefixEnd_3084956 : Nat := 4983230072969 + 3 ^ 40 * 3084956 * 2
def baseEnd_3084956 : Nat := 1056043483981158219441701

theorem tailTrace_3084956 : CollatzResearch.WordTrace tailWord_3084956 prefixEnd_3084956 1056043483981158219441701 := by
  unfold tailWord_3084956
  simp only [CollatzResearch.WordTrace]
  refine ⟨56258794505869377691881361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75011726007825836922508481 56258794505869377691881361)
  ·
    refine ⟨42194095879402033268911021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56258794505869377691881361 42194095879402033268911021)
    ·
      refine ⟨15822785954775762475841633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42194095879402033268911021 15822785954775762475841633)
      ·
        refine ⟨11867089466081821856881225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15822785954775762475841633 11867089466081821856881225)
        ·
          refine ⟨8900317099561366392660919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11867089466081821856881225 8900317099561366392660919)
          ·
            refine ⟨13350475649342049588991379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900317099561366392660919 13350475649342049588991379)
            ·
              refine ⟨20025713474013074383487069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13350475649342049588991379 20025713474013074383487069)
              ·
                refine ⟨7509642552754902893807651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20025713474013074383487069 7509642552754902893807651)
                ·
                  refine ⟨11264463829132354340711477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509642552754902893807651 11264463829132354340711477)
                  ·
                    refine ⟨1056043483981158219441701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11264463829132354340711477 1056043483981158219441701)
                    ·
                      rfl

theorem cell22_3084956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3084956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084956 prefixEnd_3084956 := by exact prefixLift 3084956
  have htrace : WordTrace (prefixWord ++ tailWord_3084956) baseStart_3084956 baseEnd_3084956 := by
    simpa [prefixWord, tailWord_3084956, baseEnd_3084956] using wordTrace_append hprefix tailTrace_3084956
  have hstable : (prefixWord ++ tailWord_3084956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084956).length < 2 ^ (prefixWord ++ tailWord_3084956).sum := by decide
  have hdescent : baseEnd_3084956 < baseStart_3084956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084977 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_3084977 : Nat := 118140960795 + 3084977 * 2 ^ 59
def prefixEnd_3084977 : Nat := 4983230072969 + 3 ^ 40 * 3084977 * 2
def baseEnd_3084977 : Nat := 1056050672710321164666637

theorem tailTrace_3084977 : CollatzResearch.WordTrace tailWord_3084977 prefixEnd_3084977 1056050672710321164666637 := by
  unfold tailWord_3084977
  simp only [CollatzResearch.WordTrace]
  refine ⟨112518354944662675970277185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75012236629775117313518123 112518354944662675970277185)
  ·
    refine ⟨84388766208497006977707889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112518354944662675970277185 84388766208497006977707889)
    ·
      refine ⟨63291574656372755233280917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84388766208497006977707889 63291574656372755233280917)
      ·
        refine ⟨2966792562017472901560043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63291574656372755233280917 2966792562017472901560043)
        ·
          refine ⟨4450188843026209352340065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966792562017472901560043 4450188843026209352340065)
          ·
            refine ⟨3337641632269657014255049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450188843026209352340065 3337641632269657014255049)
            ·
              refine ⟨2503231224202242760691287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337641632269657014255049 2503231224202242760691287)
              ·
                refine ⟨3754846836303364141036931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503231224202242760691287 3754846836303364141036931)
                ·
                  refine ⟨5632270254455046211555397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754846836303364141036931 5632270254455046211555397)
                  ·
                    refine ⟨1056050672710321164666637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632270254455046211555397 1056050672710321164666637)
                    ·
                      rfl

theorem cell22_3084977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_3084977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084977 prefixEnd_3084977 := by exact prefixLift 3084977
  have htrace : WordTrace (prefixWord ++ tailWord_3084977) baseStart_3084977 baseEnd_3084977 := by
    simpa [prefixWord, tailWord_3084977, baseEnd_3084977] using wordTrace_append hprefix tailTrace_3084977
  have hstable : (prefixWord ++ tailWord_3084977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084977).length < 2 ^ (prefixWord ++ tailWord_3084977).sum := by decide
  have hdescent : baseEnd_3084977 < baseStart_3084977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084999 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3084999 : Nat := 118140960795 + 3084999 * 2 ^ 59
def prefixEnd_3084999 : Nat := 4983230072969 + 3 ^ 40 * 3084999 * 2
def baseEnd_3084999 : Nat := 1056058203759920440616569

theorem tailTrace_3084999 : CollatzResearch.WordTrace tailWord_3084999 prefixEnd_3084999 1056058203759920440616569 := by
  unfold tailWord_3084999
  simp only [CollatzResearch.WordTrace]
  refine ⟨112519157350582973727578051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75012771567055315818385367 112519157350582973727578051)
  ·
    refine ⟨168778736025874460591367077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112519157350582973727578051 168778736025874460591367077)
    ·
      refine ⟨31646013004851461360881327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168778736025874460591367077 31646013004851461360881327)
      ·
        refine ⟨47469019507277192041321991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31646013004851461360881327 47469019507277192041321991)
        ·
          refine ⟨71203529260915788061982987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47469019507277192041321991 71203529260915788061982987)
          ·
            refine ⟨106805293891373682092974481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71203529260915788061982987 106805293891373682092974481)
            ·
              refine ⟨80103970418530261569730861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106805293891373682092974481 80103970418530261569730861)
              ·
                refine ⟨30038988906948848088649073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80103970418530261569730861 30038988906948848088649073)
                ·
                  refine ⟨22529241680211636066486805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30038988906948848088649073 22529241680211636066486805)
                  ·
                    refine ⟨1056058203759920440616569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22529241680211636066486805 1056058203759920440616569)
                    ·
                      rfl

theorem cell22_3084999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3084999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3084999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3084999 prefixEnd_3084999 := by exact prefixLift 3084999
  have htrace : WordTrace (prefixWord ++ tailWord_3084999) baseStart_3084999 baseEnd_3084999 := by
    simpa [prefixWord, tailWord_3084999, baseEnd_3084999] using wordTrace_append hprefix tailTrace_3084999
  have hstable : (prefixWord ++ tailWord_3084999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084999).length < 2 ^ (prefixWord ++ tailWord_3084999).sum := by decide
  have hdescent : baseEnd_3084999 < baseStart_3084999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085020 : List Nat := [2, 2, 5, 1, 1, 3, 2, 6]
def baseStart_3085020 : Nat := 118140960795 + 3085020 * 2 ^ 59
def prefixEnd_3085020 : Nat := 4983230072969 + 3 ^ 40 * 3085020 * 2
def baseEnd_3085020 : Nat := 117340599165453709537945

theorem tailTrace_3085020 : CollatzResearch.WordTrace tailWord_3085020 prefixEnd_3085020 117340599165453709537945 := by
  unfold tailWord_3085020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56259961641753447157046257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75013282189004596209395009 56259961641753447157046257)
  ·
    refine ⟨42194971231315085367784693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56259961641753447157046257 42194971231315085367784693)
    ·
      refine ⟨3955778552935789253229815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42194971231315085367784693 3955778552935789253229815)
      ·
        refine ⟨5933667829403683879844723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955778552935789253229815 5933667829403683879844723)
        ·
          refine ⟨8900501744105525819767085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933667829403683879844723 8900501744105525819767085)
          ·
            refine ⟨3337688154039572182412657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8900501744105525819767085 3337688154039572182412657)
            ·
              refine ⟨2503266115529679136809493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337688154039572182412657 2503266115529679136809493)
              ·
                refine ⟨117340599165453709537945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2503266115529679136809493 117340599165453709537945)
                ·
                  rfl

theorem cell22_3085020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_3085020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085020 prefixEnd_3085020 := by exact prefixLift 3085020
  have htrace : WordTrace (prefixWord ++ tailWord_3085020) baseStart_3085020 baseEnd_3085020 := by
    simpa [prefixWord, tailWord_3085020, baseEnd_3085020] using wordTrace_append hprefix tailTrace_3085020
  have hstable : (prefixWord ++ tailWord_3085020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085020).length < 2 ^ (prefixWord ++ tailWord_3085020).sum := by decide
  have hdescent : baseEnd_3085020 < baseStart_3085020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085052 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3085052 : Nat := 118140960795 + 3085052 * 2 ^ 59
def prefixEnd_3085052 : Nat := 4983230072969 + 3 ^ 40 * 3085052 * 2
def baseEnd_3085052 : Nat := 1056076346743045969041407

theorem tailTrace_3085052 : CollatzResearch.WordTrace tailWord_3085052 prefixEnd_3085052 1056076346743045969041407 := by
  unfold tailWord_3085052
  simp only [CollatzResearch.WordTrace]
  refine ⟨56260545209695481889628705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75014060279593975852838273 56260545209695481889628705)
  ·
    refine ⟨42195408907271611417221529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56260545209695481889628705 42195408907271611417221529)
    ·
      refine ⟨31646556680453708562916147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42195408907271611417221529 31646556680453708562916147)
      ·
        refine ⟨47469835020680562844374221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31646556680453708562916147 47469835020680562844374221)
        ·
          refine ⟨17801188132755211066640333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47469835020680562844374221 17801188132755211066640333)
          ·
            refine ⟨6675445549783204149990125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17801188132755211066640333 6675445549783204149990125)
            ·
              refine ⟨2503292081168701556246297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6675445549783204149990125 2503292081168701556246297)
              ·
                refine ⟨1877469060876526167184723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503292081168701556246297 1877469060876526167184723)
                ·
                  refine ⟨2816203591314789250777085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877469060876526167184723 2816203591314789250777085)
                  ·
                    refine ⟨1056076346743045969041407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816203591314789250777085 1056076346743045969041407)
                    ·
                      rfl

theorem cell22_3085052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3085052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085052 prefixEnd_3085052 := by exact prefixLift 3085052
  have htrace : WordTrace (prefixWord ++ tailWord_3085052) baseStart_3085052 baseEnd_3085052 := by
    simpa [prefixWord, tailWord_3085052, baseEnd_3085052] using wordTrace_append hprefix tailTrace_3085052
  have hstable : (prefixWord ++ tailWord_3085052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085052).length < 2 ^ (prefixWord ++ tailWord_3085052).sum := by decide
  have hdescent : baseEnd_3085052 < baseStart_3085052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085093 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 4]
def baseStart_3085093 : Nat := 118140960795 + 3085093 * 2 ^ 59
def prefixEnd_3085093 : Nat := 4983230072969 + 3 ^ 40 * 3085093 * 2
def baseEnd_3085093 : Nat := 352030127293645176255427

theorem tailTrace_3085093 : CollatzResearch.WordTrace tailWord_3085093 prefixEnd_3085093 352030127293645176255427 := by
  unfold tailWord_3085093
  simp only [CollatzResearch.WordTrace]
  refine ⟨112522585812242427781499933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75015057208161618520999955 112522585812242427781499933)
  ·
    refine ⟨42195969679590910418062475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112522585812242427781499933 42195969679590910418062475)
    ·
      refine ⟨63293954519386365627093713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42195969679590910418062475 63293954519386365627093713)
      ·
        refine ⟨47470465889539774220320285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63293954519386365627093713 47470465889539774220320285)
        ·
          refine ⟨17801424708577415332620107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47470465889539774220320285 17801424708577415332620107)
          ·
            refine ⟨26702137062866122998930161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17801424708577415332620107 26702137062866122998930161)
            ·
              refine ⟨20026602797149592249197621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26702137062866122998930161 20026602797149592249197621)
              ·
                refine ⟨1877494012232774273362277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20026602797149592249197621 1877494012232774273362277)
                ·
                  refine ⟨352030127293645176255427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877494012232774273362277 352030127293645176255427)
                  ·
                    rfl

theorem cell22_3085093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_3085093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085093 prefixEnd_3085093 := by exact prefixLift 3085093
  have htrace : WordTrace (prefixWord ++ tailWord_3085093) baseStart_3085093 baseEnd_3085093 := by
    simpa [prefixWord, tailWord_3085093, baseEnd_3085093] using wordTrace_append hprefix tailTrace_3085093
  have hstable : (prefixWord ++ tailWord_3085093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085093).length < 2 ^ (prefixWord ++ tailWord_3085093).sum := by decide
  have hdescent : baseEnd_3085093 < baseStart_3085093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085138 : List Nat := [3, 2, 2, 1, 1, 2, 5, 6]
def baseStart_3085138 : Nat := 118140960795 + 3085138 * 2 ^ 59
def prefixEnd_3085138 : Nat := 4983230072969 + 3 ^ 40 * 3085138 * 2
def baseEnd_3085138 : Nat := 117345087366730045710127

theorem tailTrace_3085138 : CollatzResearch.WordTrace tailWord_3085138 prefixEnd_3085138 117345087366730045710127 := by
  unfold tailWord_3085138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28131056774269850116722017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75016151398052933644592045 28131056774269850116722017)
  ·
    refine ⟨21098292580702387587541513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28131056774269850116722017 21098292580702387587541513)
    ·
      refine ⟨15823719435526790690656135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21098292580702387587541513 15823719435526790690656135)
      ·
        refine ⟨23735579153290186035984203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15823719435526790690656135 23735579153290186035984203)
        ·
          refine ⟨35603368729935279053976305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23735579153290186035984203 35603368729935279053976305)
          ·
            refine ⟨26702526547451459290482229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35603368729935279053976305 26702526547451459290482229)
            ·
              refine ⟨2503361863823574308482709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26702526547451459290482229 2503361863823574308482709)
              ·
                refine ⟨117345087366730045710127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2503361863823574308482709 117345087366730045710127)
                ·
                  rfl

theorem cell22_3085138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_3085138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085138 prefixEnd_3085138 := by exact prefixLift 3085138
  have htrace : WordTrace (prefixWord ++ tailWord_3085138) baseStart_3085138 baseEnd_3085138 := by
    simpa [prefixWord, tailWord_3085138, baseEnd_3085138] using wordTrace_append hprefix tailTrace_3085138
  have hstable : (prefixWord ++ tailWord_3085138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085138).length < 2 ^ (prefixWord ++ tailWord_3085138).sum := by decide
  have hdescent : baseEnd_3085138 < baseStart_3085138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085277 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3085277 : Nat := 118140960795 + 3085277 * 2 ^ 59
def prefixEnd_3085277 : Nat := 4983230072969 + 3 ^ 40 * 3085277 * 2
def baseEnd_3085277 : Nat := 1056153368841220382165717

theorem tailTrace_3085277 : CollatzResearch.WordTrace tailWord_3085277 prefixEnd_3085277 1056153368841220382165717 := by
  unfold tailWord_3085277
  simp only [CollatzResearch.WordTrace]
  refine ⟨112529296843575827206198085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75019531229050551470798723 112529296843575827206198085)
  ·
    refine ⟨21099243158170467601162141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112529296843575827206198085 21099243158170467601162141)
    ·
      refine ⟨7912216184313925350435803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21099243158170467601162141 7912216184313925350435803)
      ·
        refine ⟨11868324276470888025653705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7912216184313925350435803 11868324276470888025653705)
        ·
          refine ⟨8901243207353166019240279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11868324276470888025653705 8901243207353166019240279)
          ·
            refine ⟨13351864811029749028860419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901243207353166019240279 13351864811029749028860419)
            ·
              refine ⟨20027797216544623543290629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13351864811029749028860419 20027797216544623543290629)
              ·
                refine ⟨3755211978102116914366993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20027797216544623543290629 3755211978102116914366993)
                ·
                  refine ⟨2816408983576587685775245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3755211978102116914366993 2816408983576587685775245)
                  ·
                    refine ⟨1056153368841220382165717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816408983576587685775245 1056153368841220382165717)
                    ·
                      rfl

theorem cell22_3085277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3085277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085277 prefixEnd_3085277 := by exact prefixLift 3085277
  have htrace : WordTrace (prefixWord ++ tailWord_3085277) baseStart_3085277 baseEnd_3085277 := by
    simpa [prefixWord, tailWord_3085277, baseEnd_3085277] using wordTrace_append hprefix tailTrace_3085277
  have hstable : (prefixWord ++ tailWord_3085277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085277).length < 2 ^ (prefixWord ++ tailWord_3085277).sum := by decide
  have hdescent : baseEnd_3085277 < baseStart_3085277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085279 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 4]
def baseStart_3085279 : Nat := 118140960795 + 3085279 * 2 ^ 59
def prefixEnd_3085279 : Nat := 4983230072969 + 3 ^ 40 * 3085279 * 2
def baseEnd_3085279 : Nat := 352051351160697681205237

theorem tailTrace_3085279 : CollatzResearch.WordTrace tailWord_3085279 prefixEnd_3085279 352051351160697681205237 := by
  unfold tailWord_3085279
  simp only [CollatzResearch.WordTrace]
  refine ⟨112529369789568581547770891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75019579859712387698513927 112529369789568581547770891)
  ·
    refine ⟨168794054684352872321656337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112529369789568581547770891 168794054684352872321656337)
    ·
      refine ⟨126595541013264654241242253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168794054684352872321656337 126595541013264654241242253)
      ·
        refine ⟨47473327879974245340465845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126595541013264654241242253 47473327879974245340465845)
        ·
          refine ⟨4450624488747585500668673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47473327879974245340465845 4450624488747585500668673)
          ·
            refine ⟨3337968366560689125501505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450624488747585500668673 3337968366560689125501505)
            ·
              refine ⟨2503476274920516844126129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337968366560689125501505 2503476274920516844126129)
              ·
                refine ⟨1877607206190387633094597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503476274920516844126129 1877607206190387633094597)
                ·
                  refine ⟨352051351160697681205237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877607206190387633094597 352051351160697681205237)
                  ·
                    rfl

theorem cell22_3085279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 4].length) (baseStart_3085279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085279 prefixEnd_3085279 := by exact prefixLift 3085279
  have htrace : WordTrace (prefixWord ++ tailWord_3085279) baseStart_3085279 baseEnd_3085279 := by
    simpa [prefixWord, tailWord_3085279, baseEnd_3085279] using wordTrace_append hprefix tailTrace_3085279
  have hstable : (prefixWord ++ tailWord_3085279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085279).length < 2 ^ (prefixWord ++ tailWord_3085279).sum := by decide
  have hdescent : baseEnd_3085279 < baseStart_3085279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085290 : List Nat := [3, 1, 3, 1, 2, 4, 1, 7]
def baseStart_3085290 : Nat := 118140960795 + 3085290 * 2 ^ 59
def prefixEnd_3085290 : Nat := 4983230072969 + 3 ^ 40 * 3085290 * 2
def baseEnd_3085290 : Nat := 117350868778543631287853

theorem tailTrace_3085290 : CollatzResearch.WordTrace tailWord_3085290 prefixEnd_3085290 117350868778543631287853 := by
  unfold tailWord_3085290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28132442748132182606605331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75019847328352486950947549 28132442748132182606605331)
  ·
    refine ⟨42198664122198273909907997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28132442748132182606605331 42198664122198273909907997)
    ·
      refine ⟨15824499045824352716215499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42198664122198273909907997 15824499045824352716215499)
      ·
        refine ⟨23736748568736529074323249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15824499045824352716215499 23736748568736529074323249)
        ·
          refine ⟨17802561426552396805742437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23736748568736529074323249 17802561426552396805742437)
          ·
            refine ⟨3337980267478574401076707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17802561426552396805742437 3337980267478574401076707)
            ·
              refine ⟨5006970401217861601615061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337980267478574401076707 5006970401217861601615061)
              ·
                refine ⟨117350868778543631287853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5006970401217861601615061 117350868778543631287853)
                ·
                  rfl

theorem cell22_3085290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_3085290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085290 prefixEnd_3085290 := by exact prefixLift 3085290
  have htrace : WordTrace (prefixWord ++ tailWord_3085290) baseStart_3085290 baseEnd_3085290 := by
    simpa [prefixWord, tailWord_3085290, baseEnd_3085290] using wordTrace_append hprefix tailTrace_3085290
  have hstable : (prefixWord ++ tailWord_3085290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085290).length < 2 ^ (prefixWord ++ tailWord_3085290).sum := by decide
  have hdescent : baseEnd_3085290 < baseStart_3085290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085305 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_3085305 : Nat := 118140960795 + 3085305 * 2 ^ 59
def prefixEnd_3085305 : Nat := 4983230072969 + 3 ^ 40 * 3085305 * 2
def baseEnd_3085305 : Nat := 1056162953813437642465631

theorem tailTrace_3085305 : CollatzResearch.WordTrace tailWord_3085305 prefixEnd_3085305 1056162953813437642465631 := by
  unfold tailWord_3085305
  simp only [CollatzResearch.WordTrace]
  refine ⟨112530318087474387988217369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75020212058316258658811579 112530318087474387988217369)
  ·
    refine ⟨84397738565605790991163027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112530318087474387988217369 84397738565605790991163027)
    ·
      refine ⟨126596607848408686486744541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84397738565605790991163027 126596607848408686486744541)
      ·
        refine ⟨47473727943153257432529203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126596607848408686486744541 47473727943153257432529203)
        ·
          refine ⟨71210591914729886148793805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47473727943153257432529203 71210591914729886148793805)
          ·
            refine ⟨26703971968023707305797677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71210591914729886148793805 26703971968023707305797677)
            ·
              refine ⟨10013989488008890239674129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26703971968023707305797677 10013989488008890239674129)
              ·
                refine ⟨7510492116006667679755597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10013989488008890239674129 7510492116006667679755597)
                ·
                  refine ⟨2816434543502500379908349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7510492116006667679755597 2816434543502500379908349)
                  ·
                    refine ⟨1056162953813437642465631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816434543502500379908349 1056162953813437642465631)
                    ·
                      rfl

theorem cell22_3085305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_3085305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085305 prefixEnd_3085305 := by exact prefixLift 3085305
  have htrace : WordTrace (prefixWord ++ tailWord_3085305) baseStart_3085305 baseEnd_3085305 := by
    simpa [prefixWord, tailWord_3085305, baseEnd_3085305] using wordTrace_append hprefix tailTrace_3085305
  have hstable : (prefixWord ++ tailWord_3085305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085305).length < 2 ^ (prefixWord ++ tailWord_3085305).sum := by decide
  have hdescent : baseEnd_3085305 < baseStart_3085305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085335 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 7]
def baseStart_3085335 : Nat := 118140960795 + 3085335 * 2 ^ 59
def prefixEnd_3085335 : Nat := 4983230072969 + 3 ^ 40 * 3085335 * 2
def baseEnd_3085335 : Nat := 352057741142175854738513

theorem tailTrace_3085335 : CollatzResearch.WordTrace tailWord_3085335 prefixEnd_3085335 352057741142175854738513 := by
  unfold tailWord_3085335
  simp only [CollatzResearch.WordTrace]
  refine ⟨112531412277365703111809459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75020941518243802074539639 112531412277365703111809459)
  ·
    refine ⟨168797118416048554667714189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112531412277365703111809459 168797118416048554667714189)
    ·
      refine ⟨63298919406018208000392821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168797118416048554667714189 63298919406018208000392821)
      ·
        refine ⟨5934273694314207000036827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63298919406018208000392821 5934273694314207000036827)
        ·
          refine ⟨8901410541471310500055241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934273694314207000036827 8901410541471310500055241)
          ·
            refine ⟨6676057906103482875041431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8901410541471310500055241 6676057906103482875041431)
            ·
              refine ⟨10014086859155224312562147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676057906103482875041431 10014086859155224312562147)
              ·
                refine ⟨15021130288732836468843221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014086859155224312562147 15021130288732836468843221)
                ·
                  refine ⟨352057741142175854738513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15021130288732836468843221 352057741142175854738513)
                  ·
                    rfl

theorem cell22_3085335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_3085335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085335 prefixEnd_3085335 := by exact prefixLift 3085335
  have htrace : WordTrace (prefixWord ++ tailWord_3085335) baseStart_3085335 baseEnd_3085335 := by
    simpa [prefixWord, tailWord_3085335, baseEnd_3085335] using wordTrace_append hprefix tailTrace_3085335
  have hstable : (prefixWord ++ tailWord_3085335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085335).length < 2 ^ (prefixWord ++ tailWord_3085335).sum := by decide
  have hdescent : baseEnd_3085335 < baseStart_3085335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085416 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_3085416 : Nat := 118140960795 + 3085416 * 2 ^ 59
def prefixEnd_3085416 : Nat := 4983230072969 + 3 ^ 40 * 3085416 * 2
def baseEnd_3085416 : Nat := 1056200951381870352940291

theorem tailTrace_3085416 : CollatzResearch.WordTrace tailWord_3085416 prefixEnd_3085416 1056200951381870352940291 := by
  unfold tailWord_3085416
  simp only [CollatzResearch.WordTrace]
  refine ⟨56267183295036126972754051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75022911060048169297005401 56267183295036126972754051)
  ·
    refine ⟨84400774942554190459131077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56267183295036126972754051 84400774942554190459131077)
    ·
      refine ⟨15825145301728910711087077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84400774942554190459131077 15825145301728910711087077)
      ·
        refine ⟨2967214744074170758328827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15825145301728910711087077 2967214744074170758328827)
        ·
          refine ⟨4450822116111256137493241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967214744074170758328827 4450822116111256137493241)
          ·
            refine ⟨3338116587083442103119931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450822116111256137493241 3338116587083442103119931)
            ·
              refine ⟨5007174880625163154679897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338116587083442103119931 5007174880625163154679897)
              ·
                refine ⟨3755381160468872366009923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5007174880625163154679897 3755381160468872366009923)
                ·
                  refine ⟨5633071740703308549014885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755381160468872366009923 5633071740703308549014885)
                  ·
                    refine ⟨1056200951381870352940291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633071740703308549014885 1056200951381870352940291)
                    ·
                      rfl

theorem cell22_3085416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_3085416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085416 prefixEnd_3085416 := by exact prefixLift 3085416
  have htrace : WordTrace (prefixWord ++ tailWord_3085416) baseStart_3085416 baseEnd_3085416 := by
    simpa [prefixWord, tailWord_3085416, baseEnd_3085416] using wordTrace_append hprefix tailTrace_3085416
  have hstable : (prefixWord ++ tailWord_3085416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085416).length < 2 ^ (prefixWord ++ tailWord_3085416).sum := by decide
  have hdescent : baseEnd_3085416 < baseStart_3085416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085429 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3085429 : Nat := 118140960795 + 3085429 * 2 ^ 59
def prefixEnd_3085429 : Nat := 4983230072969 + 3 ^ 40 * 3085429 * 2
def baseEnd_3085429 : Nat := 1056205401547542652365251

theorem tailTrace_3085429 : CollatzResearch.WordTrace tailWord_3085429 prefixEnd_3085429 1056205401547542652365251 := by
  unfold tailWord_3085429
  simp only [CollatzResearch.WordTrace]
  refine ⟨112534840739025157165731341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75023227159350104777154227 112534840739025157165731341)
  ·
    refine ⟨42200565277134433937149253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112534840739025157165731341 42200565277134433937149253)
    ·
      refine ⟨7912605989462706363215485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42200565277134433937149253 7912605989462706363215485)
      ·
        refine ⟨2967227246048514886205807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7912605989462706363215485 2967227246048514886205807)
        ·
          refine ⟨4450840869072772329308711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967227246048514886205807 4450840869072772329308711)
          ·
            refine ⟨6676261303609158493963067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450840869072772329308711 6676261303609158493963067)
            ·
              refine ⟨10014391955413737740944601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676261303609158493963067 10014391955413737740944601)
              ·
                refine ⟨7510793966560303305708451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10014391955413737740944601 7510793966560303305708451)
                ·
                  refine ⟨11266190949840454958562677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7510793966560303305708451 11266190949840454958562677)
                  ·
                    refine ⟨1056205401547542652365251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11266190949840454958562677 1056205401547542652365251)
                    ·
                      rfl

theorem cell22_3085429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3085429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085429 prefixEnd_3085429 := by exact prefixLift 3085429
  have htrace : WordTrace (prefixWord ++ tailWord_3085429) baseStart_3085429 baseEnd_3085429 := by
    simpa [prefixWord, tailWord_3085429, baseEnd_3085429] using wordTrace_append hprefix tailTrace_3085429
  have hstable : (prefixWord ++ tailWord_3085429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085429).length < 2 ^ (prefixWord ++ tailWord_3085429).sum := by decide
  have hdescent : baseEnd_3085429 < baseStart_3085429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085448 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_3085448 : Nat := 118140960795 + 3085448 * 2 ^ 59
def prefixEnd_3085448 : Nat := 4983230072969 + 3 ^ 40 * 3085448 * 2
def baseEnd_3085448 : Nat := 352070635211944312046731

theorem tailTrace_3085448 : CollatzResearch.WordTrace tailWord_3085448 prefixEnd_3085448 352070635211944312046731 := by
  unfold tailWord_3085448
  simp only [CollatzResearch.WordTrace]
  refine ⟨56267766862978161705336499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75023689150637548940448665 56267766862978161705336499)
  ·
    refine ⟨84401650294467242558004749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56267766862978161705336499 84401650294467242558004749)
    ·
      refine ⟨31650618860425215959251781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84401650294467242558004749 31650618860425215959251781)
      ·
        refine ⟨5934491036329727992359709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31650618860425215959251781 5934491036329727992359709)
        ·
          refine ⟨2225434138623647997134891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5934491036329727992359709 2225434138623647997134891)
          ·
            refine ⟨3338151207935471995702337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225434138623647997134891 3338151207935471995702337)
            ·
              refine ⟨2503613405951603996776753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338151207935471995702337 2503613405951603996776753)
              ·
                refine ⟨1877710054463702997582565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503613405951603996776753 1877710054463702997582565)
                ·
                  refine ⟨352070635211944312046731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877710054463702997582565 352070635211944312046731)
                  ·
                    rfl

theorem cell22_3085448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_3085448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085448 prefixEnd_3085448 := by exact prefixLift 3085448
  have htrace : WordTrace (prefixWord ++ tailWord_3085448) baseStart_3085448 baseEnd_3085448 := by
    simpa [prefixWord, tailWord_3085448, baseEnd_3085448] using wordTrace_append hprefix tailTrace_3085448
  have hstable : (prefixWord ++ tailWord_3085448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085448).length < 2 ^ (prefixWord ++ tailWord_3085448).sum := by decide
  have hdescent : baseEnd_3085448 < baseStart_3085448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085502 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3085502 : Nat := 118140960795 + 3085502 * 2 ^ 59
def prefixEnd_3085502 : Nat := 4983230072969 + 3 ^ 40 * 3085502 * 2
def baseEnd_3085502 : Nat := 1056230390939394795290027

theorem tailTrace_3085502 : CollatzResearch.WordTrace tailWord_3085502 prefixEnd_3085502 1056230390939394795290027 := by
  unfold tailWord_3085502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14067187908470086329142345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75025002178507127088759173 14067187908470086329142345)
  ·
    refine ⟨10550390931352564746856759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14067187908470086329142345 10550390931352564746856759)
    ·
      refine ⟨15825586397028847120285139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10550390931352564746856759 15825586397028847120285139)
      ·
        refine ⟨23738379595543270680427709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15825586397028847120285139 23738379595543270680427709)
        ·
          refine ⟨8901892348328726505160391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23738379595543270680427709 8901892348328726505160391)
          ·
            refine ⟨13352838522493089757740587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901892348328726505160391 13352838522493089757740587)
            ·
              refine ⟨20029257783739634636610881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352838522493089757740587 20029257783739634636610881)
              ·
                refine ⟨15021943337804725977458161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20029257783739634636610881 15021943337804725977458161)
                ·
                  refine ⟨11266457503353544483093621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15021943337804725977458161 11266457503353544483093621)
                  ·
                    refine ⟨1056230390939394795290027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11266457503353544483093621 1056230390939394795290027)
                    ·
                      rfl

theorem cell22_3085502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3085502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085502 prefixEnd_3085502 := by exact prefixLift 3085502
  have htrace : WordTrace (prefixWord ++ tailWord_3085502) baseStart_3085502 baseEnd_3085502 := by
    simpa [prefixWord, tailWord_3085502, baseEnd_3085502] using wordTrace_append hprefix tailTrace_3085502
  have hstable : (prefixWord ++ tailWord_3085502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085502).length < 2 ^ (prefixWord ++ tailWord_3085502).sum := by decide
  have hdescent : baseEnd_3085502 < baseStart_3085502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085504 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_3085504 : Nat := 118140960795 + 3085504 * 2 ^ 59
def prefixEnd_3085504 : Nat := 4983230072969 + 3 ^ 40 * 3085504 * 2
def baseEnd_3085504 : Nat := 352077025193422485580007

theorem tailTrace_3085504 : CollatzResearch.WordTrace tailWord_3085504 prefixEnd_3085504 352077025193422485580007 := by
  unfold tailWord_3085504
  simp only [CollatzResearch.WordTrace]
  refine ⟨56268788106876722487355783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75025050809168963316474377 56268788106876722487355783)
  ·
    refine ⟨84403182160315083731033675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56268788106876722487355783 84403182160315083731033675)
    ·
      refine ⟨126604773240472625596550513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84403182160315083731033675 126604773240472625596550513)
      ·
        refine ⟨94953579930354469197412885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126604773240472625596550513 94953579930354469197412885)
        ·
          refine ⟨4450949059235365743628729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94953579930354469197412885 4450949059235365743628729)
          ·
            refine ⟨3338211794426524307721547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450949059235365743628729 3338211794426524307721547)
            ·
              refine ⟨5007317691639786461582321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338211794426524307721547 5007317691639786461582321)
              ·
                refine ⟨3755488268729839846186741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5007317691639786461582321 3755488268729839846186741)
                ·
                  refine ⟨352077025193422485580007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3755488268729839846186741 352077025193422485580007)
                  ·
                    rfl

theorem cell22_3085504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_3085504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085504 prefixEnd_3085504 := by exact prefixLift 3085504
  have htrace : WordTrace (prefixWord ++ tailWord_3085504) baseStart_3085504 baseEnd_3085504 := by
    simpa [prefixWord, tailWord_3085504, baseEnd_3085504] using wordTrace_append hprefix tailTrace_3085504
  have hstable : (prefixWord ++ tailWord_3085504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085504).length < 2 ^ (prefixWord ++ tailWord_3085504).sum := by decide
  have hdescent : baseEnd_3085504 < baseStart_3085504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085547 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 4, 3]
def baseStart_3085547 : Nat := 118140960795 + 3085547 * 2 ^ 59
def prefixEnd_3085547 : Nat := 4983230072969 + 3 ^ 40 * 3085547 * 2
def baseEnd_3085547 : Nat := 1056245795359029677914889

theorem tailTrace_3085547 : CollatzResearch.WordTrace tailWord_3085547 prefixEnd_3085547 1056245795359029677914889 := by
  unfold tailWord_3085547
  simp only [CollatzResearch.WordTrace]
  refine ⟨112539144552597663318526895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75026096368398442212351263 112539144552597663318526895)
  ·
    refine ⟨168808716828896494977790343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112539144552597663318526895 168808716828896494977790343)
    ·
      refine ⟨253213075243344742466685515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168808716828896494977790343 253213075243344742466685515)
      ·
        refine ⟨379819612865017113700028273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253213075243344742466685515 379819612865017113700028273)
        ·
          refine ⟨284864709648762835275021205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379819612865017113700028273 284864709648762835275021205)
          ·
            refine ⟨13353033264785757903516619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 284864709648762835275021205 13353033264785757903516619)
            ·
              refine ⟨20029549897178636855274929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13353033264785757903516619 20029549897178636855274929)
              ·
                refine ⟨15022162422883977641456197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20029549897178636855274929 15022162422883977641456197)
                ·
                  refine ⟨2816655454290745807773037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15022162422883977641456197 2816655454290745807773037)
                  ·
                    refine ⟨1056245795359029677914889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816655454290745807773037 1056245795359029677914889)
                    ·
                      rfl

theorem cell22_3085547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3].length) (baseStart_3085547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085547 prefixEnd_3085547 := by exact prefixLift 3085547
  have htrace : WordTrace (prefixWord ++ tailWord_3085547) baseStart_3085547 baseEnd_3085547 := by
    simpa [prefixWord, tailWord_3085547, baseEnd_3085547] using wordTrace_append hprefix tailTrace_3085547
  have hstable : (prefixWord ++ tailWord_3085547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085547).length < 2 ^ (prefixWord ++ tailWord_3085547).sum := by decide
  have hdescent : baseEnd_3085547 < baseStart_3085547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085562 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_3085562 : Nat := 118140960795 + 3085562 * 2 ^ 59
def prefixEnd_3085562 : Nat := 4983230072969 + 3 ^ 40 * 3085562 * 2
def baseEnd_3085562 : Nat := 1056250930165574638789843

theorem tailTrace_3085562 : CollatzResearch.WordTrace tailWord_3085562 prefixEnd_3085562 1056250930165574638789843 := by
  unfold tailWord_3085562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28134922911885830220080735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75026461098362213920215293 28134922911885830220080735)
  ·
    refine ⟨42202384367828745330121103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28134922911885830220080735 42202384367828745330121103)
    ·
      refine ⟨63303576551743117995181655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42202384367828745330121103 63303576551743117995181655)
      ·
        refine ⟨94955364827614676992772483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63303576551743117995181655 94955364827614676992772483)
        ·
          refine ⟨142433047241422015489158725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94955364827614676992772483 142433047241422015489158725)
          ·
            refine ⟨26706196357766627904217261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142433047241422015489158725 26706196357766627904217261)
            ·
              refine ⟨10014823634162485464081473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26706196357766627904217261 10014823634162485464081473)
              ·
                refine ⟨7511117725621864098061105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10014823634162485464081473 7511117725621864098061105)
                ·
                  refine ⟨5633338294216398073545829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7511117725621864098061105 5633338294216398073545829)
                  ·
                    refine ⟨1056250930165574638789843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633338294216398073545829 1056250930165574638789843)
                    ·
                      rfl

theorem cell22_3085562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_3085562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085562 prefixEnd_3085562 := by exact prefixLift 3085562
  have htrace : WordTrace (prefixWord ++ tailWord_3085562) baseStart_3085562 baseEnd_3085562 := by
    simpa [prefixWord, tailWord_3085562, baseEnd_3085562] using wordTrace_append hprefix tailTrace_3085562
  have hstable : (prefixWord ++ tailWord_3085562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085562).length < 2 ^ (prefixWord ++ tailWord_3085562).sum := by decide
  have hdescent : baseEnd_3085562 < baseStart_3085562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085626 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_3085626 : Nat := 118140960795 + 3085626 * 2 ^ 59
def prefixEnd_3085626 : Nat := 4983230072969 + 3 ^ 40 * 3085626 * 2
def baseEnd_3085626 : Nat := 1056272838673499805189647

theorem tailTrace_3085626 : CollatzResearch.WordTrace tailWord_3085626 prefixEnd_3085626 1056272838673499805189647 := by
  unfold tailWord_3085626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28135506479827864952663183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75028017279540973207101821 28135506479827864952663183)
  ·
    refine ⟨42203259719741797428994775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28135506479827864952663183 42203259719741797428994775)
    ·
      refine ⟨63304889579612696143492163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42203259719741797428994775 63304889579612696143492163)
      ·
        refine ⟨94957334369419044215238245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63304889579612696143492163 94957334369419044215238245)
        ·
          refine ⟨17804500194266070790357171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94957334369419044215238245 17804500194266070790357171)
          ·
            refine ⟨26706750291399106185535757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17804500194266070790357171 26706750291399106185535757)
            ·
              refine ⟨10015031359274664819575909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26706750291399106185535757 10015031359274664819575909)
              ·
                refine ⟨1877818379863999653670483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10015031359274664819575909 1877818379863999653670483)
                ·
                  refine ⟨2816727569795999480505725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877818379863999653670483 2816727569795999480505725)
                  ·
                    refine ⟨1056272838673499805189647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816727569795999480505725 1056272838673499805189647)
                    ·
                      rfl

theorem cell22_3085626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_3085626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085626 prefixEnd_3085626 := by exact prefixLift 3085626
  have htrace : WordTrace (prefixWord ++ tailWord_3085626) baseStart_3085626 baseEnd_3085626 := by
    simpa [prefixWord, tailWord_3085626, baseEnd_3085626] using wordTrace_append hprefix tailTrace_3085626
  have hstable : (prefixWord ++ tailWord_3085626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085626).length < 2 ^ (prefixWord ++ tailWord_3085626).sum := by decide
  have hdescent : baseEnd_3085626 < baseStart_3085626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085669 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_3085669 : Nat := 118140960795 + 3085669 * 2 ^ 59
def prefixEnd_3085669 : Nat := 4983230072969 + 3 ^ 40 * 3085669 * 2
def baseEnd_3085669 : Nat := 1056287558452262026364515

theorem tailTrace_3085669 : CollatzResearch.WordTrace tailWord_3085669 prefixEnd_3085669 1056287558452262026364515 := by
  unfold tailWord_3085669
  simp only [CollatzResearch.WordTrace]
  refine ⟨112543594258155678154468061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75029062838770452102978707 112543594258155678154468061)
  ·
    refine ⟨42203847846808379307925523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112543594258155678154468061 42203847846808379307925523)
    ·
      refine ⟨63305771770212568961888285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42203847846808379307925523 63305771770212568961888285)
      ·
        refine ⟨23739664413829713360708107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63305771770212568961888285 23739664413829713360708107)
        ·
          refine ⟨35609496620744570041062161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23739664413829713360708107 35609496620744570041062161)
          ·
            refine ⟨26707122465558427530796621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35609496620744570041062161 26707122465558427530796621)
            ·
              refine ⟨10015170924584410324048733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26707122465558427530796621 10015170924584410324048733)
              ·
                refine ⟨3755689096719153871518275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10015170924584410324048733 3755689096719153871518275)
                ·
                  refine ⟨5633533645078730807277413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755689096719153871518275 5633533645078730807277413)
                  ·
                    refine ⟨1056287558452262026364515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633533645078730807277413 1056287558452262026364515)
                    ·
                      rfl

theorem cell22_3085669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_3085669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085669 prefixEnd_3085669 := by exact prefixLift 3085669
  have htrace : WordTrace (prefixWord ++ tailWord_3085669) baseStart_3085669 baseEnd_3085669 := by
    simpa [prefixWord, tailWord_3085669, baseEnd_3085669] using wordTrace_append hprefix tailTrace_3085669
  have hstable : (prefixWord ++ tailWord_3085669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085669).length < 2 ^ (prefixWord ++ tailWord_3085669).sum := by decide
  have hdescent : baseEnd_3085669 < baseStart_3085669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085699 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 1, 5]
def baseStart_3085699 : Nat := 118140960795 + 3085699 * 2 ^ 59
def prefixEnd_3085699 : Nat := 4983230072969 + 3 ^ 40 * 3085699 * 2
def baseEnd_3085699 : Nat := 1056297828065351948114423

theorem tailTrace_3085699 : CollatzResearch.WordTrace tailWord_3085699 prefixEnd_3085699 1056297828065351948114423 := by
  unfold tailWord_3085699
  simp only [CollatzResearch.WordTrace]
  refine ⟨112544688448046993278060151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75029792298697995518706767 112544688448046993278060151)
  ·
    refine ⟨168817032672070489917090227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112544688448046993278060151 168817032672070489917090227)
    ·
      refine ⟨253225549008105734875635341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168817032672070489917090227 253225549008105734875635341)
      ·
        refine ⟨94959580878039650578363253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253225549008105734875635341 94959580878039650578363253)
        ·
          refine ⟨8902460707316217241721555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94959580878039650578363253 8902460707316217241721555)
          ·
            refine ⟨13353691060974325862582333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8902460707316217241721555 13353691060974325862582333)
            ·
              refine ⟨5007634147865372198468375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13353691060974325862582333 5007634147865372198468375)
              ·
                refine ⟨7511451221798058297702563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007634147865372198468375 7511451221798058297702563)
                ·
                  refine ⟨11267176832697087446553845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511451221798058297702563 11267176832697087446553845)
                  ·
                    refine ⟨1056297828065351948114423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11267176832697087446553845 1056297828065351948114423)
                    ·
                      rfl

theorem cell22_3085699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_3085699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085699 prefixEnd_3085699 := by exact prefixLift 3085699
  have htrace : WordTrace (prefixWord ++ tailWord_3085699) baseStart_3085699 baseEnd_3085699 := by
    simpa [prefixWord, tailWord_3085699, baseEnd_3085699] using wordTrace_append hprefix tailTrace_3085699
  have hstable : (prefixWord ++ tailWord_3085699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085699).length < 2 ^ (prefixWord ++ tailWord_3085699).sum := by decide
  have hdescent : baseEnd_3085699 < baseStart_3085699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085716 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3085716 : Nat := 118140960795 + 3085716 * 2 ^ 59
def prefixEnd_3085716 : Nat := 4983230072969 + 3 ^ 40 * 3085716 * 2
def baseEnd_3085716 : Nat := 1056303647512769570439371

theorem tailTrace_3085716 : CollatzResearch.WordTrace tailWord_3085716 prefixEnd_3085716 1056303647512769570439371 := by
  unfold tailWord_3085716
  simp only [CollatzResearch.WordTrace]
  refine ⟨56272654244492702590714501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75030205659323603454286001 56272654244492702590714501)
  ·
    refine ⟨10551122670842381735758969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56272654244492702590714501 10551122670842381735758969)
    ·
      refine ⟨7913342003131786301819227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10551122670842381735758969 7913342003131786301819227)
      ·
        refine ⟨11870013004697679452728841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913342003131786301819227 11870013004697679452728841)
        ·
          refine ⟨8902509753523259589546631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11870013004697679452728841 8902509753523259589546631)
          ·
            refine ⟨13353764630284889384319947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8902509753523259589546631 13353764630284889384319947)
            ·
              refine ⟨20030646945427334076479921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13353764630284889384319947 20030646945427334076479921)
              ·
                refine ⟨15022985209070500557359941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20030646945427334076479921 15022985209070500557359941)
                ·
                  refine ⟨2816809726700718854504989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15022985209070500557359941 2816809726700718854504989)
                  ·
                    refine ⟨1056303647512769570439371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816809726700718854504989 1056303647512769570439371)
                    ·
                      rfl

theorem cell22_3085716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3085716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085716 prefixEnd_3085716 := by exact prefixLift 3085716
  have htrace : WordTrace (prefixWord ++ tailWord_3085716) baseStart_3085716 baseEnd_3085716 := by
    simpa [prefixWord, tailWord_3085716, baseEnd_3085716] using wordTrace_append hprefix tailTrace_3085716
  have hstable : (prefixWord ++ tailWord_3085716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085716).length < 2 ^ (prefixWord ++ tailWord_3085716).sum := by decide
  have hdescent : baseEnd_3085716 < baseStart_3085716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085744 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_3085744 : Nat := 118140960795 + 3085744 * 2 ^ 59
def prefixEnd_3085744 : Nat := 4983230072969 + 3 ^ 40 * 3085744 * 2
def baseEnd_3085744 : Nat := 1056313232484986830739285

theorem tailTrace_3085744 : CollatzResearch.WordTrace tailWord_3085744 prefixEnd_3085744 1056313232484986830739285 := by
  unfold tailWord_3085744
  simp only [CollatzResearch.WordTrace]
  refine ⟨56273164866441982981724143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75030886488589310642298857 56273164866441982981724143)
  ·
    refine ⟨84409747299662974472586215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56273164866441982981724143 84409747299662974472586215)
    ·
      refine ⟨126614620949494461708879323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84409747299662974472586215 126614620949494461708879323)
      ·
        refine ⟨189921931424241692563318985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126614620949494461708879323 189921931424241692563318985)
        ·
          refine ⟨142441448568181269422489239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189921931424241692563318985 142441448568181269422489239)
          ·
            refine ⟨213662172852271904133733859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142441448568181269422489239 213662172852271904133733859)
            ·
              refine ⟨320493259278407856200600789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213662172852271904133733859 320493259278407856200600789)
              ·
                refine ⟨7511560764337684129701581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 320493259278407856200600789 7511560764337684129701581)
                ·
                  refine ⟨2816835286626631548638093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7511560764337684129701581 2816835286626631548638093)
                  ·
                    refine ⟨1056313232484986830739285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816835286626631548638093 1056313232484986830739285)
                    ·
                      rfl

theorem cell22_3085744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_3085744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085744 prefixEnd_3085744 := by exact prefixLift 3085744
  have htrace : WordTrace (prefixWord ++ tailWord_3085744) baseStart_3085744 baseEnd_3085744 := by
    simpa [prefixWord, tailWord_3085744, baseEnd_3085744] using wordTrace_append hprefix tailTrace_3085744
  have hstable : (prefixWord ++ tailWord_3085744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085744).length < 2 ^ (prefixWord ++ tailWord_3085744).sum := by decide
  have hdescent : baseEnd_3085744 < baseStart_3085744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085795 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 1, 3]
def baseStart_3085795 : Nat := 118140960795 + 3085795 * 2 ^ 59
def prefixEnd_3085795 : Nat := 4983230072969 + 3 ^ 40 * 3085795 * 2
def baseEnd_3085795 : Nat := 1056330690827239697714129

theorem tailTrace_3085795 : CollatzResearch.WordTrace tailWord_3085795 prefixEnd_3085795 1056330690827239697714129 := by
  unfold tailWord_3085795
  simp only [CollatzResearch.WordTrace]
  refine ⟨112548189855699201673554839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75032126570466134449036559 112548189855699201673554839)
  ·
    refine ⟨168822284783548802510332259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112548189855699201673554839 168822284783548802510332259)
    ·
      refine ⟨253233427175323203765498389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168822284783548802510332259 253233427175323203765498389)
      ·
        refine ⟨11870316898843275176507737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253233427175323203765498389 11870316898843275176507737)
        ·
          refine ⟨8902737674132456382380803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11870316898843275176507737 8902737674132456382380803)
          ·
            refine ⟨13354106511198684573571205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8902737674132456382380803 13354106511198684573571205)
            ·
              refine ⟨2503894970849753357544601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13354106511198684573571205 2503894970849753357544601)
              ·
                refine ⟨1877921228137315018158451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503894970849753357544601 1877921228137315018158451)
                ·
                  refine ⟨2816881842205972527237677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877921228137315018158451 2816881842205972527237677)
                  ·
                    refine ⟨1056330690827239697714129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816881842205972527237677 1056330690827239697714129)
                    ·
                      rfl

theorem cell22_3085795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 3].length) (baseStart_3085795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085795 prefixEnd_3085795 := by exact prefixLift 3085795
  have htrace : WordTrace (prefixWord ++ tailWord_3085795) baseStart_3085795 baseEnd_3085795 := by
    simpa [prefixWord, tailWord_3085795, baseEnd_3085795] using wordTrace_append hprefix tailTrace_3085795
  have hstable : (prefixWord ++ tailWord_3085795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085795).length < 2 ^ (prefixWord ++ tailWord_3085795).sum := by decide
  have hdescent : baseEnd_3085795 < baseStart_3085795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085838 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3085838 : Nat := 118140960795 + 3085838 * 2 ^ 59
def prefixEnd_3085838 : Nat := 4983230072969 + 3 ^ 40 * 3085838 * 2
def baseEnd_3085838 : Nat := 1056345410606001918888997

theorem tailTrace_3085838 : CollatzResearch.WordTrace tailWord_3085838 prefixEnd_3085838 1056345410606001918888997 := by
  unfold tailWord_3085838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068719774317927502171271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75033172129695613344913445 14068719774317927502171271)
  ·
    refine ⟨21103079661476891253256907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14068719774317927502171271 21103079661476891253256907)
    ·
      refine ⟨31654619492215336879885361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21103079661476891253256907 31654619492215336879885361)
      ·
        refine ⟨23740964619161502659914021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31654619492215336879885361 23740964619161502659914021)
        ·
          refine ⟨4451430866092781748733879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23740964619161502659914021 4451430866092781748733879)
          ·
            refine ⟨6677146299139172623100819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451430866092781748733879 6677146299139172623100819)
            ·
              refine ⟨10015719448708758934651229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677146299139172623100819 10015719448708758934651229)
              ·
                refine ⟨3755894793265784600494211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10015719448708758934651229 3755894793265784600494211)
                ·
                  refine ⟨5633842189898676900741317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755894793265784600494211 5633842189898676900741317)
                  ·
                    refine ⟨1056345410606001918888997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633842189898676900741317 1056345410606001918888997)
                    ·
                      rfl

theorem cell22_3085838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3085838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085838 prefixEnd_3085838 := by exact prefixLift 3085838
  have htrace : WordTrace (prefixWord ++ tailWord_3085838) baseStart_3085838 baseEnd_3085838 := by
    simpa [prefixWord, tailWord_3085838, baseEnd_3085838] using wordTrace_append hprefix tailTrace_3085838
  have hstable : (prefixWord ++ tailWord_3085838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085838).length < 2 ^ (prefixWord ++ tailWord_3085838).sum := by decide
  have hdescent : baseEnd_3085838 < baseStart_3085838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085881 : List Nat := [1, 2, 1, 5, 1, 2, 4, 6]
def baseStart_3085881 : Nat := 118140960795 + 3085881 * 2 ^ 59
def prefixEnd_3085881 : Nat := 4983230072969 + 3 ^ 40 * 3085881 * 2
def baseEnd_3085881 : Nat := 117373347820529348895985

theorem tailTrace_3085881 : CollatzResearch.WordTrace tailWord_3085881 prefixEnd_3085881 117373347820529348895985 := by
  unfold tailWord_3085881
  simp only [CollatzResearch.WordTrace]
  refine ⟨112551326533387638361185497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75034217688925092240790331 112551326533387638361185497)
  ·
    refine ⟨84413494900040728770889123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112551326533387638361185497 84413494900040728770889123)
    ·
      refine ⟨126620242350061093156333685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84413494900040728770889123 126620242350061093156333685)
      ·
        refine ⟨11870647720318227483406283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126620242350061093156333685 11870647720318227483406283)
        ·
          refine ⟨17805971580477341225109425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11870647720318227483406283 17805971580477341225109425)
          ·
            refine ⟨13354478685358005918832069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17805971580477341225109425 13354478685358005918832069)
            ·
              refine ⟨2503964753504626109781013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13354478685358005918832069 2503964753504626109781013)
              ·
                refine ⟨117373347820529348895985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2503964753504626109781013 117373347820529348895985)
                ·
                  rfl

theorem cell22_3085881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 6].length) (baseStart_3085881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085881 prefixEnd_3085881 := by exact prefixLift 3085881
  have htrace : WordTrace (prefixWord ++ tailWord_3085881) baseStart_3085881 baseEnd_3085881 := by
    simpa [prefixWord, tailWord_3085881, baseEnd_3085881] using wordTrace_append hprefix tailTrace_3085881
  have hstable : (prefixWord ++ tailWord_3085881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085881).length < 2 ^ (prefixWord ++ tailWord_3085881).sum := by decide
  have hdescent : baseEnd_3085881 < baseStart_3085881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085913 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 1, 3]
def baseStart_3085913 : Nat := 118140960795 + 3085913 * 2 ^ 59
def prefixEnd_3085913 : Nat := 4983230072969 + 3 ^ 40 * 3085913 * 2
def baseEnd_3085913 : Nat := 1056371084638726723263767

theorem tailTrace_3085913 : CollatzResearch.WordTrace tailWord_3085913 prefixEnd_3085913 1056371084638726723263767 := by
  unfold tailWord_3085913
  simp only [CollatzResearch.WordTrace]
  refine ⟨112552493669271707826350393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75034995779514471884233595 112552493669271707826350393)
  ·
    refine ⟨84414370251953780869762795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112552493669271707826350393 84414370251953780869762795)
    ·
      refine ⟨126621555377930671304644193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84414370251953780869762795 126621555377930671304644193)
      ·
        refine ⟨94966166533448003478483145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126621555377930671304644193 94966166533448003478483145)
        ·
          refine ⟨71224624900086002608862359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94966166533448003478483145 71224624900086002608862359)
          ·
            refine ⟨106836937350129003913293539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71224624900086002608862359 106836937350129003913293539)
            ·
              refine ⟨160255406025193505869940309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106836937350129003913293539 160255406025193505869940309)
              ·
                refine ⟨1877993039357736396913363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 160255406025193505869940309 1877993039357736396913363)
                ·
                  refine ⟨2816989559036604595370045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877993039357736396913363 2816989559036604595370045)
                  ·
                    refine ⟨1056371084638726723263767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816989559036604595370045 1056371084638726723263767)
                    ·
                      rfl

theorem cell22_3085913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_3085913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085913 prefixEnd_3085913 := by exact prefixLift 3085913
  have htrace : WordTrace (prefixWord ++ tailWord_3085913) baseStart_3085913 baseEnd_3085913 := by
    simpa [prefixWord, tailWord_3085913, baseEnd_3085913] using wordTrace_append hprefix tailTrace_3085913
  have hstable : (prefixWord ++ tailWord_3085913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085913).length < 2 ^ (prefixWord ++ tailWord_3085913).sum := by decide
  have hdescent : baseEnd_3085913 < baseStart_3085913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085960 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_3085960 : Nat := 118140960795 + 3085960 * 2 ^ 59
def prefixEnd_3085960 : Nat := 4983230072969 + 3 ^ 40 * 3085960 * 2
def baseEnd_3085960 : Nat := 352129057899744755779541

theorem tailTrace_3085960 : CollatzResearch.WordTrace tailWord_3085960 prefixEnd_3085960 352129057899744755779541 := by
  unfold tailWord_3085960
  simp only [CollatzResearch.WordTrace]
  refine ⟨56277103950050717426655667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75036138600067623235540889 56277103950050717426655667)
  ·
    refine ⟨84415655925076076139983501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56277103950050717426655667 84415655925076076139983501)
    ·
      refine ⟨31655870971903528552493813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84415655925076076139983501 31655870971903528552493813)
      ·
        refine ⟨2967737903615955801796295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31655870971903528552493813 2967737903615955801796295)
        ·
          refine ⟨4451606855423933702694443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967737903615955801796295 4451606855423933702694443)
          ·
            refine ⟨6677410283135900554041665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451606855423933702694443 6677410283135900554041665)
            ·
              refine ⟨5008057712351925415531249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6677410283135900554041665 5008057712351925415531249)
              ·
                refine ⟨3756043284263944061648437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008057712351925415531249 3756043284263944061648437)
                ·
                  refine ⟨352129057899744755779541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3756043284263944061648437 352129057899744755779541)
                  ·
                    rfl

theorem cell22_3085960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_3085960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3085960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3085960 prefixEnd_3085960 := by exact prefixLift 3085960
  have htrace : WordTrace (prefixWord ++ tailWord_3085960) baseStart_3085960 baseEnd_3085960 := by
    simpa [prefixWord, tailWord_3085960, baseEnd_3085960] using wordTrace_append hprefix tailTrace_3085960
  have hstable : (prefixWord ++ tailWord_3085960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085960).length < 2 ^ (prefixWord ++ tailWord_3085960).sum := by decide
  have hdescent : baseEnd_3085960 < baseStart_3085960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086022 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3086022 : Nat := 118140960795 + 3086022 * 2 ^ 59
def prefixEnd_3086022 : Nat := 4983230072969 + 3 ^ 40 * 3086022 * 2
def baseEnd_3086022 : Nat := 352136132522095590762811

theorem tailTrace_3086022 : CollatzResearch.WordTrace tailWord_3086022 prefixEnd_3086022 352136132522095590762811 := by
  unfold tailWord_3086022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517389663308650607564635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75037646150584546294712213 3517389663308650607564635)
  ·
    refine ⟨5276084494962975911346953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517389663308650607564635 5276084494962975911346953)
    ·
      refine ⟨3957063371222231933510215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5276084494962975911346953 3957063371222231933510215)
      ·
        refine ⟨5935595056833347900265323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957063371222231933510215 5935595056833347900265323)
        ·
          refine ⟨8903392585250021850397985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5935595056833347900265323 8903392585250021850397985)
          ·
            refine ⟨6677544438937516387798489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8903392585250021850397985 6677544438937516387798489)
            ·
              refine ⟨5008158329203137290848867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6677544438937516387798489 5008158329203137290848867)
              ·
                refine ⟨7512237493804705936273301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008158329203137290848867 7512237493804705936273301)
                ·
                  refine ⟨352136132522095590762811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7512237493804705936273301 352136132522095590762811)
                  ·
                    rfl

theorem cell22_3086022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3086022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086022 prefixEnd_3086022 := by exact prefixLift 3086022
  have htrace : WordTrace (prefixWord ++ tailWord_3086022) baseStart_3086022 baseEnd_3086022 := by
    simpa [prefixWord, tailWord_3086022, baseEnd_3086022] using wordTrace_append hprefix tailTrace_3086022
  have hstable : (prefixWord ++ tailWord_3086022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086022).length < 2 ^ (prefixWord ++ tailWord_3086022).sum := by decide
  have hdescent : baseEnd_3086022 < baseStart_3086022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086048 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_3086048 : Nat := 118140960795 + 3086048 * 2 ^ 59
def prefixEnd_3086048 : Nat := 4983230072969 + 3 ^ 40 * 3086048 * 2
def baseEnd_3086048 : Nat := 1056417297897631371138353

theorem tailTrace_3086048 : CollatzResearch.WordTrace tailWord_3086048 prefixEnd_3086048 1056417297897631371138353 := by
  unfold tailWord_3086048
  simp only [CollatzResearch.WordTrace]
  refine ⟨56278708761891312941257399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75038278349188417255009865 56278708761891312941257399)
  ·
    refine ⟨84418063142836969411886099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56278708761891312941257399 84418063142836969411886099)
    ·
      refine ⟨126627094714255454117829149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84418063142836969411886099 126627094714255454117829149)
      ·
        refine ⟨47485160517845795294185931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126627094714255454117829149 47485160517845795294185931)
        ·
          refine ⟨71227740776768692941278897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47485160517845795294185931 71227740776768692941278897)
          ·
            refine ⟨53420805582576519705959173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71227740776768692941278897 53420805582576519705959173)
            ·
              refine ⟨10016401046733097444867345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53420805582576519705959173 10016401046733097444867345)
              ·
                refine ⟨7512300785049823083650509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10016401046733097444867345 7512300785049823083650509)
                ·
                  refine ⟨2817112794393683656368941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7512300785049823083650509 2817112794393683656368941)
                  ·
                    refine ⟨1056417297897631371138353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817112794393683656368941 1056417297897631371138353)
                    ·
                      rfl

theorem cell22_3086048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_3086048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086048 prefixEnd_3086048 := by exact prefixLift 3086048
  have htrace : WordTrace (prefixWord ++ tailWord_3086048) baseStart_3086048 baseEnd_3086048 := by
    simpa [prefixWord, tailWord_3086048, baseEnd_3086048] using wordTrace_append hprefix tailTrace_3086048
  have hstable : (prefixWord ++ tailWord_3086048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086048).length < 2 ^ (prefixWord ++ tailWord_3086048).sum := by decide
  have hdescent : baseEnd_3086048 < baseStart_3086048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086108 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3086108 : Nat := 118140960795 + 3086108 * 2 ^ 59
def prefixEnd_3086108 : Nat := 4983230072969 + 3 ^ 40 * 3086108 * 2
def baseEnd_3086108 : Nat := 1056437837123811214638169

theorem tailTrace_3086108 : CollatzResearch.WordTrace tailWord_3086108 prefixEnd_3086108 1056437837123811214638169 := by
  unfold tailWord_3086108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56279802951782628064849489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75039737269043504086465985 56279802951782628064849489)
  ·
    refine ⟨42209852213836971048637117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56279802951782628064849489 42209852213836971048637117)
    ·
      refine ⟨15828694580188864143238919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42209852213836971048637117 15828694580188864143238919)
      ·
        refine ⟨23743041870283296214858379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15828694580188864143238919 23743041870283296214858379)
        ·
          refine ⟨35614562805424944322287569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23743041870283296214858379 35614562805424944322287569)
          ·
            refine ⟨26710922104068708241715677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35614562805424944322287569 26710922104068708241715677)
            ·
              refine ⟨10016595789025765590643379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26710922104068708241715677 10016595789025765590643379)
              ·
                refine ⟨15024893683538648385965069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10016595789025765590643379 15024893683538648385965069)
                ·
                  refine ⟨5634335131326993144736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15024893683538648385965069 5634335131326993144736901)
                  ·
                    refine ⟨1056437837123811214638169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5634335131326993144736901 1056437837123811214638169)
                    ·
                      rfl

theorem cell22_3086108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3086108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086108 prefixEnd_3086108 := by exact prefixLift 3086108
  have htrace : WordTrace (prefixWord ++ tailWord_3086108) baseStart_3086108 baseEnd_3086108 := by
    simpa [prefixWord, tailWord_3086108, baseEnd_3086108] using wordTrace_append hprefix tailTrace_3086108
  have hstable : (prefixWord ++ tailWord_3086108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086108).length < 2 ^ (prefixWord ++ tailWord_3086108).sum := by decide
  have hdescent : baseEnd_3086108 < baseStart_3086108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086206 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3086206 : Nat := 118140960795 + 3086206 * 2 ^ 59
def prefixEnd_3086206 : Nat := 4983230072969 + 3 ^ 40 * 3086206 * 2
def baseEnd_3086206 : Nat := 1056471384526571625687869

theorem tailTrace_3086206 : CollatzResearch.WordTrace tailWord_3086206 prefixEnd_3086206 1056471384526571625687869 := by
  unfold tailWord_3086206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14070397532151277358345809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75042120171473479244510981 14070397532151277358345809)
  ·
    refine ⟨10552798149113458018759357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14070397532151277358345809 10552798149113458018759357)
    ·
      refine ⟨3957299305917546757034759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10552798149113458018759357 3957299305917546757034759)
      ·
        refine ⟨5935948958876320135552139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957299305917546757034759 5935948958876320135552139)
        ·
          refine ⟨8903923438314480203328209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5935948958876320135552139 8903923438314480203328209)
          ·
            refine ⟨6677942578735860152496157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8903923438314480203328209 6677942578735860152496157)
            ·
              refine ⟨2504228467025947557186059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6677942578735860152496157 2504228467025947557186059)
              ·
                refine ⟨3756342700538921335779089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504228467025947557186059 3756342700538921335779089)
                ·
                  refine ⟨2817257025404191001834317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756342700538921335779089 2817257025404191001834317)
                  ·
                    refine ⟨1056471384526571625687869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817257025404191001834317 1056471384526571625687869)
                    ·
                      rfl

theorem cell22_3086206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3086206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086206 prefixEnd_3086206 := by exact prefixLift 3086206
  have htrace : WordTrace (prefixWord ++ tailWord_3086206) baseStart_3086206 baseEnd_3086206 := by
    simpa [prefixWord, tailWord_3086206, baseEnd_3086206] using wordTrace_append hprefix tailTrace_3086206
  have hstable : (prefixWord ++ tailWord_3086206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086206).length < 2 ^ (prefixWord ++ tailWord_3086206).sum := by decide
  have hdescent : baseEnd_3086206 < baseStart_3086206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086234 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_3086234 : Nat := 118140960795 + 3086234 * 2 ^ 59
def prefixEnd_3086234 : Nat := 4983230072969 + 3 ^ 40 * 3086234 * 2
def baseEnd_3086234 : Nat := 1056480969498788885987783

theorem tailTrace_3086234 : CollatzResearch.WordTrace tailWord_3086234 prefixEnd_3086234 1056480969498788885987783 := by
  unfold tailWord_3086234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28141050375277194912196439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75042801000739186432523837 28141050375277194912196439)
  ·
    refine ⟨42211575562915792368294659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28141050375277194912196439 42211575562915792368294659)
    ·
      refine ⟨63317363344373688552441989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42211575562915792368294659 63317363344373688552441989)
      ·
        refine ⟨11872005627070066603582873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63317363344373688552441989 11872005627070066603582873)
        ·
          refine ⟨8904004220302549952687155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11872005627070066603582873 8904004220302549952687155)
          ·
            refine ⟨13356006330453824929030733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904004220302549952687155 13356006330453824929030733)
            ·
              refine ⟨5008502373920184348386525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13356006330453824929030733 5008502373920184348386525)
              ·
                refine ⟨1878188390220069130644947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5008502373920184348386525 1878188390220069130644947)
                ·
                  refine ⟨2817282585330103695967421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878188390220069130644947 2817282585330103695967421)
                  ·
                    refine ⟨1056480969498788885987783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817282585330103695967421 1056480969498788885987783)
                    ·
                      rfl

theorem cell22_3086234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_3086234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086234 prefixEnd_3086234 := by exact prefixLift 3086234
  have htrace : WordTrace (prefixWord ++ tailWord_3086234) baseStart_3086234 baseEnd_3086234 := by
    simpa [prefixWord, tailWord_3086234, baseEnd_3086234] using wordTrace_append hprefix tailTrace_3086234
  have hstable : (prefixWord ++ tailWord_3086234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086234).length < 2 ^ (prefixWord ++ tailWord_3086234).sum := by decide
  have hdescent : baseEnd_3086234 < baseStart_3086234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086243 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_3086243 : Nat := 118140960795 + 3086243 * 2 ^ 59
def prefixEnd_3086243 : Nat := 4983230072969 + 3 ^ 40 * 3086243 * 2
def baseEnd_3086243 : Nat := 1056484050382715862512755

theorem tailTrace_3086243 : CollatzResearch.WordTrace tailWord_3086243 prefixEnd_3086243 1056484050382715862512755 := by
  unfold tailWord_3086243
  simp only [CollatzResearch.WordTrace]
  refine ⟨112564529758076174185863383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75043019838717449457242255 112564529758076174185863383)
  ·
    refine ⟨168846794637114261278795075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112564529758076174185863383 168846794637114261278795075)
    ·
      refine ⟨253270191955671391918192613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168846794637114261278795075 253270191955671391918192613)
      ·
        refine ⟨47488160991688385984661115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253270191955671391918192613 47488160991688385984661115)
        ·
          refine ⟨71232241487532578976991673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47488160991688385984661115 71232241487532578976991673)
          ·
            refine ⟨53424181115649434232743755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71232241487532578976991673 53424181115649434232743755)
            ·
              refine ⟨80136271673474151349115633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53424181115649434232743755 80136271673474151349115633)
              ·
                refine ⟨60102203755105613511836725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80136271673474151349115633 60102203755105613511836725)
                ·
                  refine ⟨5634581602041151266734693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60102203755105613511836725 5634581602041151266734693)
                  ·
                    refine ⟨1056484050382715862512755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5634581602041151266734693 1056484050382715862512755)
                    ·
                      rfl

theorem cell22_3086243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_3086243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086243 prefixEnd_3086243 := by exact prefixLift 3086243
  have htrace : WordTrace (prefixWord ++ tailWord_3086243) baseStart_3086243 baseEnd_3086243 := by
    simpa [prefixWord, tailWord_3086243, baseEnd_3086243] using wordTrace_append hprefix tailTrace_3086243
  have hstable : (prefixWord ++ tailWord_3086243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086243).length < 2 ^ (prefixWord ++ tailWord_3086243).sum := by decide
  have hdescent : baseEnd_3086243 < baseStart_3086243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086288 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_3086288 : Nat := 118140960795 + 3086288 * 2 ^ 59
def prefixEnd_3086288 : Nat := 4983230072969 + 3 ^ 40 * 3086288 * 2
def baseEnd_3086288 : Nat := 1056499454802350745137617

theorem tailTrace_3086288 : CollatzResearch.WordTrace tailWord_3086288 prefixEnd_3086288 1056499454802350745137617 := by
  unfold tailWord_3086288
  simp only [CollatzResearch.WordTrace]
  refine ⟨56283085521456573435625759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75044114028608764580834345 56283085521456573435625759)
  ·
    refine ⟨84424628282184860153438639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56283085521456573435625759 84424628282184860153438639)
    ·
      refine ⟨126636942423277290230157959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84424628282184860153438639 126636942423277290230157959)
      ·
        refine ⟨189955413634915935345236939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126636942423277290230157959 189955413634915935345236939)
        ·
          refine ⟨284933120452373903017855409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189955413634915935345236939 284933120452373903017855409)
          ·
            refine ⟨213699840339280427263391557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284933120452373903017855409 213699840339280427263391557)
            ·
              refine ⟨40068720063615080111885917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213699840339280427263391557 40068720063615080111885917)
              ·
                refine ⟨15025770023855655041957219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40068720063615080111885917 15025770023855655041957219)
                ·
                  refine ⟨22538655035783482562935829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15025770023855655041957219 22538655035783482562935829)
                  ·
                    refine ⟨1056499454802350745137617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22538655035783482562935829 1056499454802350745137617)
                    ·
                      rfl

theorem cell22_3086288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_3086288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086288 prefixEnd_3086288 := by exact prefixLift 3086288
  have htrace : WordTrace (prefixWord ++ tailWord_3086288) baseStart_3086288 baseEnd_3086288 := by
    simpa [prefixWord, tailWord_3086288, baseEnd_3086288] using wordTrace_append hprefix tailTrace_3086288
  have hstable : (prefixWord ++ tailWord_3086288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086288).length < 2 ^ (prefixWord ++ tailWord_3086288).sum := by decide
  have hdescent : baseEnd_3086288 < baseStart_3086288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086292 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3086292 : Nat := 118140960795 + 3086292 * 2 ^ 59
def prefixEnd_3086292 : Nat := 4983230072969 + 3 ^ 40 * 3086292 * 2
def baseEnd_3086292 : Nat := 352166941361365356012535

theorem tailTrace_3086292 : CollatzResearch.WordTrace tailWord_3086292 prefixEnd_3086292 352166941361365356012535 := by
  unfold tailWord_3086292
  simp only [CollatzResearch.WordTrace]
  refine ⟨56283158467449327777198565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75044211289932437036264753 56283158467449327777198565)
  ·
    refine ⟨10553092212646748958224731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56283158467449327777198565 10553092212646748958224731)
    ·
      refine ⟨15829638318970123437337097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10553092212646748958224731 15829638318970123437337097)
      ·
        refine ⟨11872228739227592578002823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15829638318970123437337097 11872228739227592578002823)
        ·
          refine ⟨17808343108841388867004235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11872228739227592578002823 17808343108841388867004235)
          ·
            refine ⟨26712514663262083300506353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17808343108841388867004235 26712514663262083300506353)
            ·
              refine ⟨20034385997446562475379765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26712514663262083300506353 20034385997446562475379765)
              ·
                refine ⟨1878223687260615232066853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20034385997446562475379765 1878223687260615232066853)
                ·
                  refine ⟨352166941361365356012535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878223687260615232066853 352166941361365356012535)
                  ·
                    rfl

theorem cell22_3086292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3086292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086292 prefixEnd_3086292 := by exact prefixLift 3086292
  have htrace : WordTrace (prefixWord ++ tailWord_3086292) baseStart_3086292 baseEnd_3086292 := by
    simpa [prefixWord, tailWord_3086292, baseEnd_3086292] using wordTrace_append hprefix tailTrace_3086292
  have hstable : (prefixWord ++ tailWord_3086292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086292).length < 2 ^ (prefixWord ++ tailWord_3086292).sum := by decide
  have hdescent : baseEnd_3086292 < baseStart_3086292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086303 : List Nat := [1, 1, 2, 3, 4, 11]
def baseStart_3086303 : Nat := 118140960795 + 3086303 * 2 ^ 59
def prefixEnd_3086303 : Nat := 4983230072969 + 3 ^ 40 * 3086303 * 2
def baseEnd_3086303 : Nat := 13043266538381428469291

theorem tailTrace_3086303 : CollatzResearch.WordTrace tailWord_3086303 prefixEnd_3086303 13043266538381428469291 := by
  unfold tailWord_3086303
  simp only [CollatzResearch.WordTrace]
  refine ⟨112566718137858804433047563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75044478758572536288698375 112566718137858804433047563)
  ·
    refine ⟨168850077206788206649571345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112566718137858804433047563 168850077206788206649571345)
    ·
      refine ⟨126637557905091154987178509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168850077206788206649571345 126637557905091154987178509)
      ·
        refine ⟨47489084214409183120191941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126637557905091154987178509 47489084214409183120191941)
        ·
          refine ⟨8904203290201721835035989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47489084214409183120191941 8904203290201721835035989)
          ·
            refine ⟨13043266538381428469291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8904203290201721835035989 13043266538381428469291)
            ·
              rfl

theorem cell22_3086303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 11].length) (baseStart_3086303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086303 prefixEnd_3086303 := by exact prefixLift 3086303
  have htrace : WordTrace (prefixWord ++ tailWord_3086303) baseStart_3086303 baseEnd_3086303 := by
    simpa [prefixWord, tailWord_3086303, baseEnd_3086303] using wordTrace_append hprefix tailTrace_3086303
  have hstable : (prefixWord ++ tailWord_3086303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086303).length < 2 ^ (prefixWord ++ tailWord_3086303).sum := by decide
  have hdescent : baseEnd_3086303 < baseStart_3086303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086305 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3086305 : Nat := 118140960795 + 3086305 * 2 ^ 59
def prefixEnd_3086305 : Nat := 4983230072969 + 3 ^ 40 * 3086305 * 2
def baseEnd_3086305 : Nat := 1056505274249768367462565

theorem tailTrace_3086305 : CollatzResearch.WordTrace tailWord_3086305 prefixEnd_3086305 1056505274249768367462565 := by
  unfold tailWord_3086305
  simp only [CollatzResearch.WordTrace]
  refine ⟨112566791083851558774620369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75044527389234372516413579 112566791083851558774620369)
  ·
    refine ⟨84425093312888669080965277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112566791083851558774620369 84425093312888669080965277)
    ·
      refine ⟨31659409992333250905361979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84425093312888669080965277 31659409992333250905361979)
      ·
        refine ⟨47489114988499876358042969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31659409992333250905361979 47489114988499876358042969)
        ·
          refine ⟨35616836241374907268532227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47489114988499876358042969 35616836241374907268532227)
          ·
            refine ⟨53425254362062360902798341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35616836241374907268532227 53425254362062360902798341)
            ·
              refine ⟨10017235192886692669274689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53425254362062360902798341 10017235192886692669274689)
              ·
                refine ⟨7512926394665019501956017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10017235192886692669274689 7512926394665019501956017)
                ·
                  refine ⟨5634694795998764626467013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7512926394665019501956017 5634694795998764626467013)
                  ·
                    refine ⟨1056505274249768367462565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5634694795998764626467013 1056505274249768367462565)
                    ·
                      rfl

theorem cell22_3086305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3086305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086305 prefixEnd_3086305 := by exact prefixLift 3086305
  have htrace : WordTrace (prefixWord ++ tailWord_3086305) baseStart_3086305 baseEnd_3086305 := by
    simpa [prefixWord, tailWord_3086305, baseEnd_3086305] using wordTrace_append hprefix tailTrace_3086305
  have hstable : (prefixWord ++ tailWord_3086305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086305).length < 2 ^ (prefixWord ++ tailWord_3086305).sum := by decide
  have hdescent : baseEnd_3086305 < baseStart_3086305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086307 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 2, 3]
def baseStart_3086307 : Nat := 118140960795 + 3086307 * 2 ^ 59
def prefixEnd_3086307 : Nat := 4983230072969 + 3 ^ 40 * 3086307 * 2
def baseEnd_3086307 : Nat := 1056505958890641028912559

theorem tailTrace_3086307 : CollatzResearch.WordTrace tailWord_3086307 prefixEnd_3086307 1056505958890641028912559 := by
  unfold tailWord_3086307
  simp only [CollatzResearch.WordTrace]
  refine ⟨112566864029844313116193175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75044576019896208744128783 112566864029844313116193175)
  ·
    refine ⟨168850296044766469674289763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112566864029844313116193175 168850296044766469674289763)
    ·
      refine ⟨253275444067149704511434645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168850296044766469674289763 253275444067149704511434645)
      ·
        refine ⟨11872286440647642398973499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253275444067149704511434645 11872286440647642398973499)
        ·
          refine ⟨17808429660971463598460249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11872286440647642398973499 17808429660971463598460249)
          ·
            refine ⟨13356322245728597698845187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17808429660971463598460249 13356322245728597698845187)
            ·
              refine ⟨20034483368592896548267781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13356322245728597698845187 20034483368592896548267781)
              ·
                refine ⟨3756465631611168102800209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20034483368592896548267781 3756465631611168102800209)
                ·
                  refine ⟨2817349223708376077100157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756465631611168102800209 2817349223708376077100157)
                  ·
                    refine ⟨1056505958890641028912559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817349223708376077100157 1056505958890641028912559)
                    ·
                      rfl

theorem cell22_3086307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3].length) (baseStart_3086307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086307 prefixEnd_3086307 := by exact prefixLift 3086307
  have htrace : WordTrace (prefixWord ++ tailWord_3086307) baseStart_3086307 baseEnd_3086307 := by
    simpa [prefixWord, tailWord_3086307, baseEnd_3086307] using wordTrace_append hprefix tailTrace_3086307
  have hstable : (prefixWord ++ tailWord_3086307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086307).length < 2 ^ (prefixWord ++ tailWord_3086307).sum := by decide
  have hdescent : baseEnd_3086307 < baseStart_3086307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086369 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_3086369 : Nat := 118140960795 + 3086369 * 2 ^ 59
def prefixEnd_3086369 : Nat := 4983230072969 + 3 ^ 40 * 3086369 * 2
def baseEnd_3086369 : Nat := 1056527182757693533862369

theorem tailTrace_3086369 : CollatzResearch.WordTrace tailWord_3086369 prefixEnd_3086369 1056527182757693533862369 := by
  unfold tailWord_3086369
  simp only [CollatzResearch.WordTrace]
  refine ⟨112569125355619697704950161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75046083570413131803300107 112569125355619697704950161)
  ·
    refine ⟨84426844016714773278712621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112569125355619697704950161 84426844016714773278712621)
    ·
      refine ⟨31660066506268039979517233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84426844016714773278712621 31660066506268039979517233)
      ·
        refine ⟨23745049879701029984637925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31660066506268039979517233 23745049879701029984637925)
        ·
          refine ⟨4452196852443943122119611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23745049879701029984637925 4452196852443943122119611)
          ·
            refine ⟨6678295278665914683179417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452196852443943122119611 6678295278665914683179417)
            ·
              refine ⟨5008721458999436012384563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678295278665914683179417 5008721458999436012384563)
              ·
                refine ⟨7513082188499154018576845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008721458999436012384563 7513082188499154018576845)
                ·
                  refine ⟨2817405820687182756966317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7513082188499154018576845 2817405820687182756966317)
                  ·
                    refine ⟨1056527182757693533862369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817405820687182756966317 1056527182757693533862369)
                    ·
                      rfl

theorem cell22_3086369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_3086369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086369 prefixEnd_3086369 := by exact prefixLift 3086369
  have htrace : WordTrace (prefixWord ++ tailWord_3086369) baseStart_3086369 baseEnd_3086369 := by
    simpa [prefixWord, tailWord_3086369, baseEnd_3086369] using wordTrace_append hprefix tailTrace_3086369
  have hstable : (prefixWord ++ tailWord_3086369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086369).length < 2 ^ (prefixWord ++ tailWord_3086369).sum := by decide
  have hdescent : baseEnd_3086369 < baseStart_3086369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086412 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_3086412 : Nat := 118140960795 + 3086412 * 2 ^ 59
def prefixEnd_3086412 : Nat := 4983230072969 + 3 ^ 40 * 3086412 * 2
def baseEnd_3086412 : Nat := 1056541902536455755037237

theorem tailTrace_3086412 : CollatzResearch.WordTrace tailWord_3086412 prefixEnd_3086412 1056541902536455755037237 := by
  unfold tailWord_3086412
  simp only [CollatzResearch.WordTrace]
  refine ⟨56285346847231958024382745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75047129129642610699176993 56285346847231958024382745)
  ·
    refine ⟨42214010135423968518287059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56285346847231958024382745 42214010135423968518287059)
    ·
      refine ⟨63321015203135952777430589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42214010135423968518287059 63321015203135952777430589)
      ·
        refine ⟨23745380701175982291536471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63321015203135952777430589 23745380701175982291536471)
        ·
          refine ⟨35618071051763973437304707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23745380701175982291536471 35618071051763973437304707)
          ·
            refine ⟨53427106577645960155957061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35618071051763973437304707 53427106577645960155957061)
            ·
              refine ⟨10017582483308617529241949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53427106577645960155957061 10017582483308617529241949)
              ·
                refine ⟨3756593431240731573465731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10017582483308617529241949 3756593431240731573465731)
                ·
                  refine ⟨5634890146861097360198597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756593431240731573465731 5634890146861097360198597)
                  ·
                    refine ⟨1056541902536455755037237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5634890146861097360198597 1056541902536455755037237)
                    ·
                      rfl

theorem cell22_3086412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_3086412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086412 prefixEnd_3086412 := by exact prefixLift 3086412
  have htrace : WordTrace (prefixWord ++ tailWord_3086412) baseStart_3086412 baseEnd_3086412 := by
    simpa [prefixWord, tailWord_3086412, baseEnd_3086412] using wordTrace_append hprefix tailTrace_3086412
  have hstable : (prefixWord ++ tailWord_3086412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086412).length < 2 ^ (prefixWord ++ tailWord_3086412).sum := by decide
  have hdescent : baseEnd_3086412 < baseStart_3086412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086455 : List Nat := [1, 1, 3, 1, 1, 5, 2, 8]
def baseStart_3086455 : Nat := 118140960795 + 3086455 * 2 ^ 59
def prefixEnd_3086455 : Nat := 4983230072969 + 3 ^ 40 * 3086455 * 2
def baseEnd_3086455 : Nat := 117395180257246441801345

theorem tailTrace_3086455 : CollatzResearch.WordTrace tailWord_3086455 prefixEnd_3086455 117395180257246441801345 := by
  unfold tailWord_3086455
  simp only [CollatzResearch.WordTrace]
  refine ⟨112572262033308134392580819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75048174688872089595053879 112572262033308134392580819)
  ·
    refine ⟨168858393049962201588871229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112572262033308134392580819 168858393049962201588871229)
    ·
      refine ⟨63321897393735825595826711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168858393049962201588871229 63321897393735825595826711)
      ·
        refine ⟨94982846090603738393740067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63321897393735825595826711 94982846090603738393740067)
        ·
          refine ⟨142474269135905607590610101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94982846090603738393740067 142474269135905607590610101)
          ·
            refine ⟨13356962731491150711619697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142474269135905607590610101 13356962731491150711619697)
            ·
              refine ⟨10017722048618363033714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13356962731491150711619697 10017722048618363033714773)
              ·
                refine ⟨117395180257246441801345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10017722048618363033714773 117395180257246441801345)
                ·
                  rfl

theorem cell22_3086455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 8].length) (baseStart_3086455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086455 prefixEnd_3086455 := by exact prefixLift 3086455
  have htrace : WordTrace (prefixWord ++ tailWord_3086455) baseStart_3086455 baseEnd_3086455 := by
    simpa [prefixWord, tailWord_3086455, baseEnd_3086455] using wordTrace_append hprefix tailTrace_3086455
  have hstable : (prefixWord ++ tailWord_3086455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086455).length < 2 ^ (prefixWord ++ tailWord_3086455).sum := by decide
  have hdescent : baseEnd_3086455 < baseStart_3086455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086457 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_3086457 : Nat := 118140960795 + 3086457 * 2 ^ 59
def prefixEnd_3086457 : Nat := 4983230072969 + 3 ^ 40 * 3086457 * 2
def baseEnd_3086457 : Nat := 1056557306956090637662099

theorem tailTrace_3086457 : CollatzResearch.WordTrace tailWord_3086457 prefixEnd_3086457 1056557306956090637662099 := by
  unfold tailWord_3086457
  simp only [CollatzResearch.WordTrace]
  refine ⟨112572334979300888734153625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75048223319533925822769083 112572334979300888734153625)
  ·
    refine ⟨84429251234475666550615219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112572334979300888734153625 84429251234475666550615219)
    ·
      refine ⟨126643876851713499825922829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84429251234475666550615219 126643876851713499825922829)
      ·
        refine ⟨47491453819392562434721061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126643876851713499825922829 47491453819392562434721061)
        ·
          refine ⟨8904647591136105456510199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47491453819392562434721061 8904647591136105456510199)
          ·
            refine ⟨13356971386704158184765299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904647591136105456510199 13356971386704158184765299)
            ·
              refine ⟨20035457080056237277147949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13356971386704158184765299 20035457080056237277147949)
              ·
                refine ⟨7513296405021088978930481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20035457080056237277147949 7513296405021088978930481)
                ·
                  refine ⟨5634972303765816734197861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513296405021088978930481 5634972303765816734197861)
                  ·
                    refine ⟨1056557306956090637662099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5634972303765816734197861 1056557306956090637662099)
                    ·
                      rfl

theorem cell22_3086457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_3086457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086457 prefixEnd_3086457 := by exact prefixLift 3086457
  have htrace : WordTrace (prefixWord ++ tailWord_3086457) baseStart_3086457 baseEnd_3086457 := by
    simpa [prefixWord, tailWord_3086457, baseEnd_3086457] using wordTrace_append hprefix tailTrace_3086457
  have hstable : (prefixWord ++ tailWord_3086457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086457).length < 2 ^ (prefixWord ++ tailWord_3086457).sum := by decide
  have hdescent : baseEnd_3086457 < baseStart_3086457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086478 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_3086478 : Nat := 118140960795 + 3086478 * 2 ^ 59
def prefixEnd_3086478 : Nat := 4983230072969 + 3 ^ 40 * 3086478 * 2
def baseEnd_3086478 : Nat := 352188165228417860962345

theorem tailTrace_3086478 : CollatzResearch.WordTrace tailWord_3086478 prefixEnd_3086478 352188165228417860962345 := by
  unfold tailWord_3086478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071637614028101165083511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75048733941483206213778725 14071637614028101165083511)
  ·
    refine ⟨21107456421042151747625267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14071637614028101165083511 21107456421042151747625267)
    ·
      refine ⟨31661184631563227621437901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21107456421042151747625267 31661184631563227621437901)
      ·
        refine ⟨11872944236836210358039213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31661184631563227621437901 11872944236836210358039213)
        ·
          refine ⟨4452354088813578884264705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11872944236836210358039213 4452354088813578884264705)
          ·
            refine ⟨3339265566610184163198529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452354088813578884264705 3339265566610184163198529)
            ·
              refine ⟨2504449174957638122398897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339265566610184163198529 2504449174957638122398897)
              ·
                refine ⟨1878336881218228591799173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504449174957638122398897 1878336881218228591799173)
                ·
                  refine ⟨352188165228417860962345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878336881218228591799173 352188165228417860962345)
                  ·
                    rfl

theorem cell22_3086478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_3086478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086478 prefixEnd_3086478 := by exact prefixLift 3086478
  have htrace : WordTrace (prefixWord ++ tailWord_3086478) baseStart_3086478 baseEnd_3086478 := by
    simpa [prefixWord, tailWord_3086478, baseEnd_3086478] using wordTrace_append hprefix tailTrace_3086478
  have hstable : (prefixWord ++ tailWord_3086478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086478).length < 2 ^ (prefixWord ++ tailWord_3086478).sum := by decide
  have hdescent : baseEnd_3086478 < baseStart_3086478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086485 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3086485 : Nat := 118140960795 + 3086485 * 2 ^ 59
def prefixEnd_3086485 : Nat := 4983230072969 + 3 ^ 40 * 3086485 * 2
def baseEnd_3086485 : Nat := 1056566891928307897962013

theorem tailTrace_3086485 : CollatzResearch.WordTrace tailWord_3086485 prefixEnd_3086485 1056566891928307897962013 := by
  unfold tailWord_3086485
  simp only [CollatzResearch.WordTrace]
  refine ⟨112573356223199449516172909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75048904148799633010781939 112573356223199449516172909)
  ·
    refine ⟨42215008583699793568564841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112573356223199449516172909 42215008583699793568564841)
    ·
      refine ⟨31661256437774845176423631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42215008583699793568564841 31661256437774845176423631)
      ·
        refine ⟨47491884656662267764635447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31661256437774845176423631 47491884656662267764635447)
        ·
          refine ⟨71237826984993401646953171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47491884656662267764635447 71237826984993401646953171)
          ·
            refine ⟨106856740477490102470429757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71237826984993401646953171 106856740477490102470429757)
            ·
              refine ⟨40071277679058788426411159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106856740477490102470429757 40071277679058788426411159)
              ·
                refine ⟨60106916518588182639616739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40071277679058788426411159 60106916518588182639616739)
                ·
                  refine ⟨90160374777882273959425109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60106916518588182639616739 90160374777882273959425109)
                  ·
                    refine ⟨1056566891928307897962013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90160374777882273959425109 1056566891928307897962013)
                    ·
                      rfl

theorem cell22_3086485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3086485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086485 prefixEnd_3086485 := by exact prefixLift 3086485
  have htrace : WordTrace (prefixWord ++ tailWord_3086485) baseStart_3086485 baseEnd_3086485 := by
    simpa [prefixWord, tailWord_3086485, baseEnd_3086485] using wordTrace_append hprefix tailTrace_3086485
  have hstable : (prefixWord ++ tailWord_3086485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086485).length < 2 ^ (prefixWord ++ tailWord_3086485).sum := by decide
  have hdescent : baseEnd_3086485 < baseStart_3086485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086506 : List Nat := [3, 1, 5, 1, 2, 1, 3, 6]
def baseStart_3086506 : Nat := 118140960795 + 3086506 * 2 ^ 59
def prefixEnd_3086506 : Nat := 4983230072969 + 3 ^ 40 * 3086506 * 2
def baseEnd_3086506 : Nat := 117397120073052315909661

theorem tailTrace_3086506 : CollatzResearch.WordTrace tailWord_3086506 prefixEnd_3086506 117397120073052315909661 := by
  unfold tailWord_3086506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28143530539030842525671843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75049414770748913401791581 28143530539030842525671843)
  ·
    refine ⟨42215295808546263788507765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28143530539030842525671843 42215295808546263788507765)
    ·
      refine ⟨3957683982051212230172603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42215295808546263788507765 3957683982051212230172603)
      ·
        refine ⟨5936525973076818345258905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957683982051212230172603 5936525973076818345258905)
        ·
          refine ⟨4452394479807613758944179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5936525973076818345258905 4452394479807613758944179)
          ·
            refine ⟨6678591719711420638416269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452394479807613758944179 6678591719711420638416269)
            ·
              refine ⟨2504471894891782739406101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678591719711420638416269 2504471894891782739406101)
              ·
                refine ⟨117397120073052315909661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2504471894891782739406101 117397120073052315909661)
                ·
                  rfl

theorem cell22_3086506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_3086506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086506 prefixEnd_3086506 := by exact prefixLift 3086506
  have htrace : WordTrace (prefixWord ++ tailWord_3086506) baseStart_3086506 baseEnd_3086506 := by
    simpa [prefixWord, tailWord_3086506, baseEnd_3086506] using wordTrace_append hprefix tailTrace_3086506
  have hstable : (prefixWord ++ tailWord_3086506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086506).length < 2 ^ (prefixWord ++ tailWord_3086506).sum := by decide
  have hdescent : baseEnd_3086506 < baseStart_3086506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086515 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_3086515 : Nat := 118140960795 + 3086515 * 2 ^ 59
def prefixEnd_3086515 : Nat := 4983230072969 + 3 ^ 40 * 3086515 * 2
def baseEnd_3086515 : Nat := 1056577161541397819711921

theorem tailTrace_3086515 : CollatzResearch.WordTrace tailWord_3086515 prefixEnd_3086515 1056577161541397819711921 := by
  unfold tailWord_3086515
  simp only [CollatzResearch.WordTrace]
  refine ⟨112574450413090764639764999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75049633608727176426509999 112574450413090764639764999)
  ·
    refine ⟨168861675619636146959647499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112574450413090764639764999 168861675619636146959647499)
    ·
      refine ⟨253292513429454220439471249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168861675619636146959647499 253292513429454220439471249)
      ·
        refine ⟨189969385072090665329603437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253292513429454220439471249 189969385072090665329603437)
        ·
          refine ⟨71238519402033999498601289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189969385072090665329603437 71238519402033999498601289)
          ·
            refine ⟨53428889551525499623950967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71238519402033999498601289 53428889551525499623950967)
            ·
              refine ⟨80143334327288249435926451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53428889551525499623950967 80143334327288249435926451)
              ·
                refine ⟨120215001490932374153889677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80143334327288249435926451 120215001490932374153889677)
                ·
                  refine ⟨45080625559099640307708629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120215001490932374153889677 45080625559099640307708629)
                  ·
                    refine ⟨1056577161541397819711921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45080625559099640307708629 1056577161541397819711921)
                    ·
                      rfl

theorem cell22_3086515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_3086515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086515 prefixEnd_3086515 := by exact prefixLift 3086515
  have htrace : WordTrace (prefixWord ++ tailWord_3086515) baseStart_3086515 baseEnd_3086515 := by
    simpa [prefixWord, tailWord_3086515, baseEnd_3086515] using wordTrace_append hprefix tailTrace_3086515
  have hstable : (prefixWord ++ tailWord_3086515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086515).length < 2 ^ (prefixWord ++ tailWord_3086515).sum := by decide
  have hdescent : baseEnd_3086515 < baseStart_3086515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086521 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 1, 3]
def baseStart_3086521 : Nat := 118140960795 + 3086521 * 2 ^ 59
def prefixEnd_3086521 : Nat := 4983230072969 + 3 ^ 40 * 3086521 * 2
def baseEnd_3086521 : Nat := 1056579215464015804061903

theorem tailTrace_3086521 : CollatzResearch.WordTrace tailWord_3086521 prefixEnd_3086521 1056579215464015804061903 := by
  unfold tailWord_3086521
  simp only [CollatzResearch.WordTrace]
  refine ⟨112574669251069027664483417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75049779500712685109655611 112574669251069027664483417)
  ·
    refine ⟨84431001938301770748362563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112574669251069027664483417 84431001938301770748362563)
    ·
      refine ⟨126646502907452656122543845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84431001938301770748362563 126646502907452656122543845)
      ·
        refine ⟨23746219295147373022976971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126646502907452656122543845 23746219295147373022976971)
        ·
          refine ⟨35619328942721059534465457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23746219295147373022976971 35619328942721059534465457)
          ·
            refine ⟨26714496707040794650849093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35619328942721059534465457 26714496707040794650849093)
            ·
              refine ⟨5008968132570148997034205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26714496707040794650849093 5008968132570148997034205)
              ·
                refine ⟨1878363049713805873887827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5008968132570148997034205 1878363049713805873887827)
                ·
                  refine ⟨2817544574570708810831741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878363049713805873887827 2817544574570708810831741)
                  ·
                    refine ⟨1056579215464015804061903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817544574570708810831741 1056579215464015804061903)
                    ·
                      rfl

theorem cell22_3086521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_3086521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086521 prefixEnd_3086521 := by exact prefixLift 3086521
  have htrace : WordTrace (prefixWord ++ tailWord_3086521) baseStart_3086521 baseEnd_3086521 := by
    simpa [prefixWord, tailWord_3086521, baseEnd_3086521] using wordTrace_append hprefix tailTrace_3086521
  have hstable : (prefixWord ++ tailWord_3086521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086521).length < 2 ^ (prefixWord ++ tailWord_3086521).sum := by decide
  have hdescent : baseEnd_3086521 < baseStart_3086521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086577 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3086577 : Nat := 118140960795 + 3086577 * 2 ^ 59
def prefixEnd_3086577 : Nat := 4983230072969 + 3 ^ 40 * 3086577 * 2
def baseEnd_3086577 : Nat := 1056598385408450324661731

theorem tailTrace_3086577 : CollatzResearch.WordTrace tailWord_3086577 prefixEnd_3086577 1056598385408450324661731 := by
  unfold tailWord_3086577
  simp only [CollatzResearch.WordTrace]
  refine ⟨112576711738866149228521985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75051141159244099485681323 112576711738866149228521985)
  ·
    refine ⟨84432533804149611921391489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112576711738866149228521985 84432533804149611921391489)
    ·
      refine ⟨63324400353112208941043617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84432533804149611921391489 63324400353112208941043617)
      ·
        refine ⟨47493300264834156705782713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63324400353112208941043617 47493300264834156705782713)
        ·
          refine ⟨35619975198625617529337035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47493300264834156705782713 35619975198625617529337035)
          ·
            refine ⟨53429962797938426294005553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35619975198625617529337035 53429962797938426294005553)
            ·
              refine ⟨40072472098453819720504165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53429962797938426294005553 40072472098453819720504165)
              ·
                refine ⟨7513588518460091197594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40072472098453819720504165 7513588518460091197594531)
                ·
                  refine ⟨11270382777690136796391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7513588518460091197594531 11270382777690136796391797)
                  ·
                    refine ⟨1056598385408450324661731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11270382777690136796391797 1056598385408450324661731)
                    ·
                      rfl

theorem cell22_3086577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3086577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086577 prefixEnd_3086577 := by exact prefixLift 3086577
  have htrace : WordTrace (prefixWord ++ tailWord_3086577) baseStart_3086577 baseEnd_3086577 := by
    simpa [prefixWord, tailWord_3086577, baseEnd_3086577] using wordTrace_append hprefix tailTrace_3086577
  have hstable : (prefixWord ++ tailWord_3086577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086577).length < 2 ^ (prefixWord ++ tailWord_3086577).sum := by decide
  have hdescent : baseEnd_3086577 < baseStart_3086577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086592 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_3086592 : Nat := 118140960795 + 3086592 * 2 ^ 59
def prefixEnd_3086592 : Nat := 4983230072969 + 3 ^ 40 * 3086592 * 2
def baseEnd_3086592 : Nat := 1056603520214995285536685

theorem tailTrace_3086592 : CollatzResearch.WordTrace tailWord_3086592 prefixEnd_3086592 1056603520214995285536685 := by
  unfold tailWord_3086592
  simp only [CollatzResearch.WordTrace]
  refine ⟨56288629416905903395159015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75051505889207871193545353 56288629416905903395159015)
  ·
    refine ⟨84432944125358855092738523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56288629416905903395159015 84432944125358855092738523)
    ·
      refine ⟨126649416188038282639107785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84432944125358855092738523 126649416188038282639107785)
      ·
        refine ⟨94987062141028711979330839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126649416188038282639107785 94987062141028711979330839)
        ·
          refine ⟨142480593211543067968996259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94987062141028711979330839 142480593211543067968996259)
          ·
            refine ⟨213720889817314601953494389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142480593211543067968996259 213720889817314601953494389)
            ·
              refine ⟨20036333420373243933140099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213720889817314601953494389 20036333420373243933140099)
              ·
                refine ⟨30054500130559865899710149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20036333420373243933140099 30054500130559865899710149)
                ·
                  refine ⟨5635218774479974856195653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30054500130559865899710149 5635218774479974856195653)
                  ·
                    refine ⟨1056603520214995285536685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635218774479974856195653 1056603520214995285536685)
                    ·
                      rfl

theorem cell22_3086592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_3086592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086592 prefixEnd_3086592 := by exact prefixLift 3086592
  have htrace : WordTrace (prefixWord ++ tailWord_3086592) baseStart_3086592 baseEnd_3086592 := by
    simpa [prefixWord, tailWord_3086592, baseEnd_3086592] using wordTrace_append hprefix tailTrace_3086592
  have hstable : (prefixWord ++ tailWord_3086592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086592).length < 2 ^ (prefixWord ++ tailWord_3086592).sum := by decide
  have hdescent : baseEnd_3086592 < baseStart_3086592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086596 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3086596 : Nat := 118140960795 + 3086596 * 2 ^ 59
def prefixEnd_3086596 : Nat := 4983230072969 + 3 ^ 40 * 3086596 * 2
def baseEnd_3086596 : Nat := 352201629832246869478891

theorem tailTrace_3086596 : CollatzResearch.WordTrace tailWord_3086596 prefixEnd_3086596 352201629832246869478891 := by
  unfold tailWord_3086596
  simp only [CollatzResearch.WordTrace]
  refine ⟨56288702362898657736731821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75051603150531543648975761 56288702362898657736731821)
  ·
    refine ⟨21108263386086996651274433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56288702362898657736731821 21108263386086996651274433)
    ·
      refine ⟨15831197539565247488455825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21108263386086996651274433 15831197539565247488455825)
      ·
        refine ⟨11873398154673935616341869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15831197539565247488455825 11873398154673935616341869)
        ·
          refine ⟨4452524308002725856128201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11873398154673935616341869 4452524308002725856128201)
          ·
            refine ⟨3339393231002044392096151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452524308002725856128201 3339393231002044392096151)
            ·
              refine ⟨5009089846503066588144227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339393231002044392096151 5009089846503066588144227)
              ·
                refine ⟨7513634769754599882216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009089846503066588144227 7513634769754599882216341)
                ·
                  refine ⟨352201629832246869478891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7513634769754599882216341 352201629832246869478891)
                  ·
                    rfl

theorem cell22_3086596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3086596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086596 prefixEnd_3086596 := by exact prefixLift 3086596
  have htrace : WordTrace (prefixWord ++ tailWord_3086596) baseStart_3086596 baseEnd_3086596 := by
    simpa [prefixWord, tailWord_3086596, baseEnd_3086596] using wordTrace_append hprefix tailTrace_3086596
  have hstable : (prefixWord ++ tailWord_3086596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086596).length < 2 ^ (prefixWord ++ tailWord_3086596).sum := by decide
  have hdescent : baseEnd_3086596 < baseStart_3086596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086626 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3086626 : Nat := 118140960795 + 3086626 * 2 ^ 59
def prefixEnd_3086626 : Nat := 4983230072969 + 3 ^ 40 * 3086626 * 2
def baseEnd_3086626 : Nat := 1056615159109830530186581

theorem tailTrace_3086626 : CollatzResearch.WordTrace tailWord_3086626 prefixEnd_3086626 1056615159109830530186581 := by
  unfold tailWord_3086626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28144624728922157649263933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75052332610459087064703821 28144624728922157649263933)
  ·
    refine ⟨10554234273345809118473975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28144624728922157649263933 10554234273345809118473975)
    ·
      refine ⟨15831351410018713677710963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554234273345809118473975 15831351410018713677710963)
      ·
        refine ⟨23747027115028070516566445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15831351410018713677710963 23747027115028070516566445)
        ·
          refine ⟨8905135168135526443712417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23747027115028070516566445 8905135168135526443712417)
          ·
            refine ⟨6678851376101644832784313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8905135168135526443712417 6678851376101644832784313)
            ·
              refine ⟨5009138532076233624588235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678851376101644832784313 5009138532076233624588235)
              ·
                refine ⟨7513707798114350436882353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009138532076233624588235 7513707798114350436882353)
                ·
                  refine ⟨5635280848585762827661765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513707798114350436882353 5635280848585762827661765)
                  ·
                    refine ⟨1056615159109830530186581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635280848585762827661765 1056615159109830530186581)
                    ·
                      rfl

theorem cell22_3086626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3086626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086626 prefixEnd_3086626 := by exact prefixLift 3086626
  have htrace : WordTrace (prefixWord ++ tailWord_3086626) baseStart_3086626 baseEnd_3086626 := by
    simpa [prefixWord, tailWord_3086626, baseEnd_3086626] using wordTrace_append hprefix tailTrace_3086626
  have hstable : (prefixWord ++ tailWord_3086626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086626).length < 2 ^ (prefixWord ++ tailWord_3086626).sum := by decide
  have hdescent : baseEnd_3086626 < baseStart_3086626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086654 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3086654 : Nat := 118140960795 + 3086654 * 2 ^ 59
def prefixEnd_3086654 : Nat := 4983230072969 + 3 ^ 40 * 3086654 * 2
def baseEnd_3086654 : Nat := 1056624744082047790486495

theorem tailTrace_3086654 : CollatzResearch.WordTrace tailWord_3086654 prefixEnd_3086654 1056624744082047790486495 := by
  unfold tailWord_3086654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072440019948398922384377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75053013439724794252716677 14072440019948398922384377)
  ·
    refine ⟨10554330014961299191788283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14072440019948398922384377 10554330014961299191788283)
    ·
      refine ⟨15831495022441948787682425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554330014961299191788283 15831495022441948787682425)
      ·
        refine ⟨11873621266831461590761819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15831495022441948787682425 11873621266831461590761819)
        ·
          refine ⟨17810431900247192386142729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873621266831461590761819 17810431900247192386142729)
          ·
            refine ⟨13357823925185394289607047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17810431900247192386142729 13357823925185394289607047)
            ·
              refine ⟨20036735887778091434410571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357823925185394289607047 20036735887778091434410571)
              ·
                refine ⟨30055103831667137151615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20036735887778091434410571 30055103831667137151615857)
                ·
                  refine ⟨22541327873750352863711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30055103831667137151615857 22541327873750352863711893)
                  ·
                    refine ⟨1056624744082047790486495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22541327873750352863711893 1056624744082047790486495)
                    ·
                      rfl

theorem cell22_3086654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3086654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086654 prefixEnd_3086654 := by exact prefixLift 3086654
  have htrace : WordTrace (prefixWord ++ tailWord_3086654) baseStart_3086654 baseEnd_3086654 := by
    simpa [prefixWord, tailWord_3086654, baseEnd_3086654] using wordTrace_append hprefix tailTrace_3086654
  have hstable : (prefixWord ++ tailWord_3086654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086654).length < 2 ^ (prefixWord ++ tailWord_3086654).sum := by decide
  have hdescent : baseEnd_3086654 < baseStart_3086654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086690 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3086690 : Nat := 118140960795 + 3086690 * 2 ^ 59
def prefixEnd_3086690 : Nat := 4983230072969 + 3 ^ 40 * 3086690 * 2
def baseEnd_3086690 : Nat := 1056637067617755696586385

theorem tailTrace_3086690 : CollatzResearch.WordTrace tailWord_3086690 prefixEnd_3086690 1056637067617755696586385 := by
  unfold tailWord_3086690
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145208296864192381846381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75053888791637846351590349 28145208296864192381846381)
  ·
    refine ⟨10554453111324072143192393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28145208296864192381846381 10554453111324072143192393)
    ·
      refine ⟨7915839833493054107394295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10554453111324072143192393 7915839833493054107394295)
      ·
        refine ⟨11873759750239581161091443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915839833493054107394295 11873759750239581161091443)
        ·
          refine ⟨17810639625359371741637165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873759750239581161091443 17810639625359371741637165)
          ·
            refine ⟨6678989859509764403113937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17810639625359371741637165 6678989859509764403113937)
            ·
              refine ⟨5009242394632323302335453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678989859509764403113937 5009242394632323302335453)
              ·
                refine ⟨1878465897987121238375795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5009242394632323302335453 1878465897987121238375795)
                ·
                  refine ⟨2817698846980681857563693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878465897987121238375795 2817698846980681857563693)
                  ·
                    refine ⟨1056637067617755696586385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817698846980681857563693 1056637067617755696586385)
                    ·
                      rfl

theorem cell22_3086690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3086690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086690 prefixEnd_3086690 := by exact prefixLift 3086690
  have htrace : WordTrace (prefixWord ++ tailWord_3086690) baseStart_3086690 baseEnd_3086690 := by
    simpa [prefixWord, tailWord_3086690, baseEnd_3086690] using wordTrace_append hprefix tailTrace_3086690
  have hstable : (prefixWord ++ tailWord_3086690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086690).length < 2 ^ (prefixWord ++ tailWord_3086690).sum := by decide
  have hdescent : baseEnd_3086690 < baseStart_3086690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086697 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 8]
def baseStart_3086697 : Nat := 118140960795 + 3086697 * 2 ^ 59
def prefixEnd_3086697 : Nat := 4983230072969 + 3 ^ 40 * 3086697 * 2
def baseEnd_3086697 : Nat := 352213154620270003887121

theorem tailTrace_3086697 : CollatzResearch.WordTrace tailWord_3086697 prefixEnd_3086697 352213154620270003887121 := by
  unfold tailWord_3086697
  simp only [CollatzResearch.WordTrace]
  refine ⟨112581088498431409722890345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75054058998954273148593563 112581088498431409722890345)
  ·
    refine ⟨84435816373823557292167759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112581088498431409722890345 84435816373823557292167759)
    ·
      refine ⟨126653724560735335938251639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84435816373823557292167759 126653724560735335938251639)
      ·
        refine ⟨189980586841103003907377459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126653724560735335938251639 189980586841103003907377459)
        ·
          refine ⟨284970880261654505861066189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189980586841103003907377459 284970880261654505861066189)
          ·
            refine ⟨106864080098120439697899821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284970880261654505861066189 106864080098120439697899821)
            ·
              refine ⟨40074030036795164886712433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106864080098120439697899821 40074030036795164886712433)
              ·
                refine ⟨30055522527596373665034325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40074030036795164886712433 30055522527596373665034325)
                ·
                  refine ⟨352213154620270003887121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30055522527596373665034325 352213154620270003887121)
                  ·
                    rfl

theorem cell22_3086697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_3086697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086697 prefixEnd_3086697 := by exact prefixLift 3086697
  have htrace : WordTrace (prefixWord ++ tailWord_3086697) baseStart_3086697 baseEnd_3086697 := by
    simpa [prefixWord, tailWord_3086697, baseEnd_3086697] using wordTrace_append hprefix tailTrace_3086697
  have hstable : (prefixWord ++ tailWord_3086697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086697).length < 2 ^ (prefixWord ++ tailWord_3086697).sum := by decide
  have hdescent : baseEnd_3086697 < baseStart_3086697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086699 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 1, 4]
def baseStart_3086699 : Nat := 118140960795 + 3086699 * 2 ^ 59
def prefixEnd_3086699 : Nat := 4983230072969 + 3 ^ 40 * 3086699 * 2
def baseEnd_3086699 : Nat := 1056640148501682673111357

theorem tailTrace_3086699 : CollatzResearch.WordTrace tailWord_3086699 prefixEnd_3086699 1056640148501682673111357 := by
  unfold tailWord_3086699
  simp only [CollatzResearch.WordTrace]
  refine ⟨112581161444424164064463151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75054107629616109376308767 112581161444424164064463151)
  ·
    refine ⟨168871742166636246096694727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112581161444424164064463151 168871742166636246096694727)
    ·
      refine ⟨253307613249954369145042091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168871742166636246096694727 253307613249954369145042091)
      ·
        refine ⟨379961419874931553717563137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253307613249954369145042091 379961419874931553717563137)
        ·
          refine ⟨284971064906198665288172353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379961419874931553717563137 284971064906198665288172353)
          ·
            refine ⟨213728298679648998966129265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284971064906198665288172353 213728298679648998966129265)
            ·
              refine ⟨160296224009736749224596949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213728298679648998966129265 160296224009736749224596949)
              ·
                refine ⟨3756942750228205059951491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160296224009736749224596949 3756942750228205059951491)
                ·
                  refine ⟨5635414125342307589927237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756942750228205059951491 5635414125342307589927237)
                  ·
                    refine ⟨1056640148501682673111357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635414125342307589927237 1056640148501682673111357)
                    ·
                      rfl

theorem cell22_3086699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4].length) (baseStart_3086699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086699 prefixEnd_3086699 := by exact prefixLift 3086699
  have htrace : WordTrace (prefixWord ++ tailWord_3086699) baseStart_3086699 baseEnd_3086699 := by
    simpa [prefixWord, tailWord_3086699, baseEnd_3086699] using wordTrace_append hprefix tailTrace_3086699
  have hstable : (prefixWord ++ tailWord_3086699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086699).length < 2 ^ (prefixWord ++ tailWord_3086699).sum := by decide
  have hdescent : baseEnd_3086699 < baseStart_3086699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086712 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3086712 : Nat := 118140960795 + 3086712 * 2 ^ 59
def prefixEnd_3086712 : Nat := 4983230072969 + 3 ^ 40 * 3086712 * 2
def baseEnd_3086712 : Nat := 1056644598667354972536317

theorem tailTrace_3086712 : CollatzResearch.WordTrace tailWord_3086712 prefixEnd_3086712 1056644598667354972536317 := by
  unfold tailWord_3086712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56290817796688533642343195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75054423728918044856457593 56290817796688533642343195)
  ·
    refine ⟨84436226695032800463514793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56290817796688533642343195 84436226695032800463514793)
    ·
      refine ⟨63327170021274600347636095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84436226695032800463514793 63327170021274600347636095)
      ·
        refine ⟨94990755031911900521454143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63327170021274600347636095 94990755031911900521454143)
        ·
          refine ⟨142486132547867850782181215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94990755031911900521454143 142486132547867850782181215)
          ·
            refine ⟨213729198821801776173271823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142486132547867850782181215 213729198821801776173271823)
            ·
              refine ⟨320593798232702664259907735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213729198821801776173271823 320593798232702664259907735)
              ·
                refine ⟨480890697349053996389861603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320593798232702664259907735 480890697349053996389861603)
                ·
                  refine ⟨721336046023580994584792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480890697349053996389861603 721336046023580994584792405)
                  ·
                    refine ⟨1056644598667354972536317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 721336046023580994584792405 1056644598667354972536317)
                    ·
                      rfl

theorem cell22_3086712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3086712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086712 prefixEnd_3086712 := by exact prefixLift 3086712
  have htrace : WordTrace (prefixWord ++ tailWord_3086712) baseStart_3086712 baseEnd_3086712 := by
    simpa [prefixWord, tailWord_3086712, baseEnd_3086712] using wordTrace_append hprefix tailTrace_3086712
  have hstable : (prefixWord ++ tailWord_3086712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086712).length < 2 ^ (prefixWord ++ tailWord_3086712).sum := by decide
  have hdescent : baseEnd_3086712 < baseStart_3086712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086746 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_3086746 : Nat := 118140960795 + 3086746 * 2 ^ 59
def prefixEnd_3086746 : Nat := 4983230072969 + 3 ^ 40 * 3086746 * 2
def baseEnd_3086746 : Nat := 1056656237562190217186213

theorem tailTrace_3086746 : CollatzResearch.WordTrace tailWord_3086746 prefixEnd_3086746 1056656237562190217186213 := by
  unfold tailWord_3086746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145718918813472772856023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75055250450169260727616061 28145718918813472772856023)
  ·
    refine ⟨42218578378220209159284035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28145718918813472772856023 42218578378220209159284035)
    ·
      refine ⟨63327867567330313738926053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42218578378220209159284035 63327867567330313738926053)
      ·
        refine ⟨11873975168874433826048635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63327867567330313738926053 11873975168874433826048635)
        ·
          refine ⟨17810962753311650739072953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873975168874433826048635 17810962753311650739072953)
          ·
            refine ⟨13358222064983738054304715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17810962753311650739072953 13358222064983738054304715)
            ·
              refine ⟨20037333097475607081457073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13358222064983738054304715 20037333097475607081457073)
              ·
                refine ⟨15027999823106705311092805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20037333097475607081457073 15027999823106705311092805)
                ·
                  refine ⟨2817749966832507245829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15027999823106705311092805 2817749966832507245829901)
                  ·
                    refine ⟨1056656237562190217186213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817749966832507245829901 1056656237562190217186213)
                    ·
                      rfl

theorem cell22_3086746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_3086746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086746 prefixEnd_3086746 := by exact prefixLift 3086746
  have htrace : WordTrace (prefixWord ++ tailWord_3086746) baseStart_3086746 baseEnd_3086746 := by
    simpa [prefixWord, tailWord_3086746, baseEnd_3086746] using wordTrace_append hprefix tailTrace_3086746
  have hstable : (prefixWord ++ tailWord_3086746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086746).length < 2 ^ (prefixWord ++ tailWord_3086746).sum := by decide
  have hdescent : baseEnd_3086746 < baseStart_3086746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086759 : List Nat := [1, 1, 6, 1, 1, 2, 10]
def baseStart_3086759 : Nat := 118140960795 + 3086759 * 2 ^ 59
def prefixEnd_3086759 : Nat := 4983230072969 + 3 ^ 40 * 3086759 * 2
def baseEnd_3086759 : Nat := 39135581026957870985599

theorem tailTrace_3086759 : CollatzResearch.WordTrace tailWord_3086759 prefixEnd_3086759 39135581026957870985599 := by
  unfold tailWord_3086759
  simp only [CollatzResearch.WordTrace]
  refine ⟨112583349824206794311647331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75055566549471196207764887 112583349824206794311647331)
  ·
    refine ⟨168875024736310191467470997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112583349824206794311647331 168875024736310191467470997)
    ·
      refine ⟨7916016784514540225037703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168875024736310191467470997 7916016784514540225037703)
      ·
        refine ⟨11874025176771810337556555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7916016784514540225037703 11874025176771810337556555)
        ·
          refine ⟨17811037765157715506334833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11874025176771810337556555 17811037765157715506334833)
          ·
            refine ⟨13358278323868286629751125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17811037765157715506334833 13358278323868286629751125)
            ·
              refine ⟨39135581026957870985599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13358278323868286629751125 39135581026957870985599)
              ·
                rfl

theorem cell22_3086759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 10].length) (baseStart_3086759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086759 prefixEnd_3086759 := by exact prefixLift 3086759
  have htrace : WordTrace (prefixWord ++ tailWord_3086759) baseStart_3086759 baseEnd_3086759 := by
    simpa [prefixWord, tailWord_3086759, baseEnd_3086759] using wordTrace_append hprefix tailTrace_3086759
  have hstable : (prefixWord ++ tailWord_3086759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086759).length < 2 ^ (prefixWord ++ tailWord_3086759).sum := by decide
  have hdescent : baseEnd_3086759 < baseStart_3086759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086765 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 6]
def baseStart_3086765 : Nat := 118140960795 + 3086765 * 2 ^ 59
def prefixEnd_3086765 : Nat := 4983230072969 + 3 ^ 40 * 3086765 * 2
def baseEnd_3086765 : Nat := 352220913883493500320385

theorem tailTrace_3086765 : CollatzResearch.WordTrace tailWord_3086765 prefixEnd_3086765 352220913883493500320385 := by
  unfold tailWord_3086765
  simp only [CollatzResearch.WordTrace]
  refine ⟨112583568662185057336365749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75055712441456704890910499 112583568662185057336365749)
  ·
    refine ⟨10554709562079849125284289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112583568662185057336365749 10554709562079849125284289)
    ·
      refine ⟨7916032171559886843963217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10554709562079849125284289 7916032171559886843963217)
      ·
        refine ⟨5937024128669915132972413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7916032171559886843963217 5937024128669915132972413)
        ·
          refine ⟨2226384048251218174864655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5937024128669915132972413 2226384048251218174864655)
          ·
            refine ⟨3339576072376827262296983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226384048251218174864655 3339576072376827262296983)
            ·
              refine ⟨5009364108565240893445475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339576072376827262296983 5009364108565240893445475)
              ·
                refine ⟨7514046162847861340168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009364108565240893445475 7514046162847861340168213)
                ·
                  refine ⟨352220913883493500320385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7514046162847861340168213 352220913883493500320385)
                  ·
                    rfl

theorem cell22_3086765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_3086765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086765 prefixEnd_3086765 := by exact prefixLift 3086765
  have htrace : WordTrace (prefixWord ++ tailWord_3086765) baseStart_3086765 baseEnd_3086765 := by
    simpa [prefixWord, tailWord_3086765, baseEnd_3086765] using wordTrace_append hprefix tailTrace_3086765
  have hstable : (prefixWord ++ tailWord_3086765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086765).length < 2 ^ (prefixWord ++ tailWord_3086765).sum := by decide
  have hdescent : baseEnd_3086765 < baseStart_3086765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086780 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3086780 : Nat := 118140960795 + 3086780 * 2 ^ 59
def prefixEnd_3086780 : Nat := 4983230072969 + 3 ^ 40 * 3086780 * 2
def baseEnd_3086780 : Nat := 1056667876457025461836109

theorem tailTrace_3086780 : CollatzResearch.WordTrace tailWord_3086780 prefixEnd_3086780 1056667876457025461836109 := by
  unfold tailWord_3086780
  simp only [CollatzResearch.WordTrace]
  refine ⟨56292057878565357449080897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75056077171420476598774529 56292057878565357449080897)
  ·
    refine ⟨42219043408924018086810673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56292057878565357449080897 42219043408924018086810673)
    ·
      refine ⟨31664282556693013565108005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42219043408924018086810673 31664282556693013565108005)
      ·
        refine ⟨5937052979379940043457751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31664282556693013565108005 5937052979379940043457751)
        ·
          refine ⟨8905579469069910065186627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5937052979379940043457751 8905579469069910065186627)
          ·
            refine ⟨13358369203604865097779941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905579469069910065186627 13358369203604865097779941)
            ·
              refine ⟨2504694225675912205833739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13358369203604865097779941 2504694225675912205833739)
              ·
                refine ⟨3757041338513868308750609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504694225675912205833739 3757041338513868308750609)
                ·
                  refine ⟨2817781003885401231562957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757041338513868308750609 2817781003885401231562957)
                  ·
                    refine ⟨1056667876457025461836109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817781003885401231562957 1056667876457025461836109)
                    ·
                      rfl

theorem cell22_3086780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3086780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086780 prefixEnd_3086780 := by exact prefixLift 3086780
  have htrace : WordTrace (prefixWord ++ tailWord_3086780) baseStart_3086780 baseEnd_3086780 := by
    simpa [prefixWord, tailWord_3086780, baseEnd_3086780] using wordTrace_append hprefix tailTrace_3086780
  have hstable : (prefixWord ++ tailWord_3086780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086780).length < 2 ^ (prefixWord ++ tailWord_3086780).sum := by decide
  have hdescent : baseEnd_3086780 < baseStart_3086780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086808 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 1, 3]
def baseStart_3086808 : Nat := 118140960795 + 3086808 * 2 ^ 59
def prefixEnd_3086808 : Nat := 4983230072969 + 3 ^ 40 * 3086808 * 2
def baseEnd_3086808 : Nat := 1056677461429242722136023

theorem tailTrace_3086808 : CollatzResearch.WordTrace tailWord_3086808 prefixEnd_3086808 1056677461429242722136023 := by
  unfold tailWord_3086808
  simp only [CollatzResearch.WordTrace]
  refine ⟨56292568500514637840090539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75056758000686183786787385 56292568500514637840090539)
  ·
    refine ⟨84438852750771956760135809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56292568500514637840090539 84438852750771956760135809)
    ·
      refine ⟨63329139563078967570101857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84438852750771956760135809 63329139563078967570101857)
      ·
        refine ⟨47496854672309225677576393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63329139563078967570101857 47496854672309225677576393)
        ·
          refine ⟨35622641004231919258182295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47496854672309225677576393 35622641004231919258182295)
          ·
            refine ⟨53433961506347878887273443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35622641004231919258182295 53433961506347878887273443)
            ·
              refine ⟨80150942259521818330910165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53433961506347878887273443 80150942259521818330910165)
              ·
                refine ⟨1878537709207542617130707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80150942259521818330910165 1878537709207542617130707)
                ·
                  refine ⟨2817806563811313925696061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878537709207542617130707 2817806563811313925696061)
                  ·
                    refine ⟨1056677461429242722136023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817806563811313925696061 1056677461429242722136023)
                    ·
                      rfl

theorem cell22_3086808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_3086808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086808 prefixEnd_3086808 := by exact prefixLift 3086808
  have htrace : WordTrace (prefixWord ++ tailWord_3086808) baseStart_3086808 baseEnd_3086808 := by
    simpa [prefixWord, tailWord_3086808, baseEnd_3086808] using wordTrace_append hprefix tailTrace_3086808
  have hstable : (prefixWord ++ tailWord_3086808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086808).length < 2 ^ (prefixWord ++ tailWord_3086808).sum := by decide
  have hdescent : baseEnd_3086808 < baseStart_3086808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086851 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 1, 4]
def baseStart_3086851 : Nat := 118140960795 + 3086851 * 2 ^ 59
def prefixEnd_3086851 : Nat := 4983230072969 + 3 ^ 40 * 3086851 * 2
def baseEnd_3086851 : Nat := 1056692181208004943310891

theorem tailTrace_3086851 : CollatzResearch.WordTrace tailWord_3086851 prefixEnd_3086851 1056692181208004943310891 := by
  unfold tailWord_3086851
  simp only [CollatzResearch.WordTrace]
  refine ⟨112586705339873494023996407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75057803559915662682664271 112586705339873494023996407)
  ·
    refine ⟨168880058009810241035994611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112586705339873494023996407 168880058009810241035994611)
    ·
      refine ⟨253320087014715361553991917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168880058009810241035994611 253320087014715361553991917)
      ·
        refine ⟨94995032630518260582746969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253320087014715361553991917 94995032630518260582746969)
        ·
          refine ⟨71246274472888695437060227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94995032630518260582746969 71246274472888695437060227)
          ·
            refine ⟨106869411709333043155590341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71246274472888695437060227 106869411709333043155590341)
            ·
              refine ⟨20038014695499945591673189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106869411709333043155590341 20038014695499945591673189)
              ·
                refine ⟨3757127755406239798438723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20038014695499945591673189 3757127755406239798438723)
                ·
                  refine ⟨5635691633109359697658085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757127755406239798438723 5635691633109359697658085)
                  ·
                    refine ⟨1056692181208004943310891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635691633109359697658085 1056692181208004943310891)
                    ·
                      rfl

theorem cell22_3086851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4].length) (baseStart_3086851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086851 prefixEnd_3086851 := by exact prefixLift 3086851
  have htrace : WordTrace (prefixWord ++ tailWord_3086851) baseStart_3086851 baseEnd_3086851 := by
    simpa [prefixWord, tailWord_3086851, baseEnd_3086851] using wordTrace_append hprefix tailTrace_3086851
  have hstable : (prefixWord ++ tailWord_3086851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086851).length < 2 ^ (prefixWord ++ tailWord_3086851).sum := by decide
  have hdescent : baseEnd_3086851 < baseStart_3086851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086864 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_3086864 : Nat := 118140960795 + 3086864 * 2 ^ 59
def prefixEnd_3086864 : Nat := 4983230072969 + 3 ^ 40 * 3086864 * 2
def baseEnd_3086864 : Nat := 1056696631373677242735851

theorem tailTrace_3086864 : CollatzResearch.WordTrace tailWord_3086864 prefixEnd_3086864 1056696631373677242735851 := by
  unfold tailWord_3086864
  simp only [CollatzResearch.WordTrace]
  refine ⟨56293589744413198622109823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75058119659217598162813097 56293589744413198622109823)
  ·
    refine ⟨84440384616619797933164735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56293589744413198622109823 84440384616619797933164735)
    ·
      refine ⟨126660576924929696899747103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84440384616619797933164735 126660576924929696899747103)
      ·
        refine ⟨189990865387394545349620655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126660576924929696899747103 189990865387394545349620655)
        ·
          refine ⟨284986298081091818024430983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189990865387394545349620655 284986298081091818024430983)
          ·
            refine ⟨427479447121637727036646475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284986298081091818024430983 427479447121637727036646475)
            ·
              refine ⟨641219170682456590554969713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427479447121637727036646475 641219170682456590554969713)
              ·
                refine ⟨480914378011842442916227285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641219170682456590554969713 480914378011842442916227285)
                ·
                  refine ⟨11271430734652557255849077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 480914378011842442916227285 11271430734652557255849077)
                  ·
                    refine ⟨1056696631373677242735851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11271430734652557255849077 1056696631373677242735851)
                    ·
                      rfl

theorem cell22_3086864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_3086864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086864 prefixEnd_3086864 := by exact prefixLift 3086864
  have htrace : WordTrace (prefixWord ++ tailWord_3086864) baseStart_3086864 baseEnd_3086864 := by
    simpa [prefixWord, tailWord_3086864, baseEnd_3086864] using wordTrace_append hprefix tailTrace_3086864
  have hstable : (prefixWord ++ tailWord_3086864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086864).length < 2 ^ (prefixWord ++ tailWord_3086864).sum := by decide
  have hdescent : baseEnd_3086864 < baseStart_3086864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086883 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 4]
def baseStart_3086883 : Nat := 118140960795 + 3086883 * 2 ^ 59
def prefixEnd_3086883 : Nat := 4983230072969 + 3 ^ 40 * 3086883 * 2
def baseEnd_3086883 : Nat := 352234378487322508836931

theorem tailTrace_3086883 : CollatzResearch.WordTrace tailWord_3086883 prefixEnd_3086883 352234378487322508836931 := by
  unfold tailWord_3086883
  simp only [CollatzResearch.WordTrace]
  refine ⟨112587872475757563489161303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75058581650505042326107535 112587872475757563489161303)
  ·
    refine ⟨168881808713636345233741955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112587872475757563489161303 168881808713636345233741955)
    ·
      refine ⟨253322713070454517850612933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168881808713636345233741955 253322713070454517850612933)
      ·
        refine ⟨47498008700710222096989925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253322713070454517850612933 47498008700710222096989925)
        ·
          refine ⟨8905876631383166643185611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47498008700710222096989925 8905876631383166643185611)
          ·
            refine ⟨13358814947074749964778417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905876631383166643185611 13358814947074749964778417)
            ·
              refine ⟨10019111210306062473583813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13358814947074749964778417 10019111210306062473583813)
              ·
                refine ⟨1878583351932386713796965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10019111210306062473583813 1878583351932386713796965)
                ·
                  refine ⟨352234378487322508836931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878583351932386713796965 352234378487322508836931)
                  ·
                    rfl

theorem cell22_3086883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 4].length) (baseStart_3086883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086883 prefixEnd_3086883 := by exact prefixLift 3086883
  have htrace : WordTrace (prefixWord ++ tailWord_3086883) baseStart_3086883 baseEnd_3086883 := by
    simpa [prefixWord, tailWord_3086883, baseEnd_3086883] using wordTrace_append hprefix tailTrace_3086883
  have hstable : (prefixWord ++ tailWord_3086883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086883).length < 2 ^ (prefixWord ++ tailWord_3086883).sum := by decide
  have hdescent : baseEnd_3086883 < baseStart_3086883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086898 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_3086898 : Nat := 118140960795 + 3086898 * 2 ^ 59
def prefixEnd_3086898 : Nat := 4983230072969 + 3 ^ 40 * 3086898 * 2
def baseEnd_3086898 : Nat := 1056708270268512487385747

theorem tailTrace_3086898 : CollatzResearch.WordTrace tailWord_3086898 prefixEnd_3086898 1056708270268512487385747 := by
  unfold tailWord_3086898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28147104892675805262739337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75058946380468814033971565 28147104892675805262739337)
  ·
    refine ⟨21110328669506853947054503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28147104892675805262739337 21110328669506853947054503)
    ·
      refine ⟨31665493004260280920581755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21110328669506853947054503 31665493004260280920581755)
      ·
        refine ⟨47498239506390421380872633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31665493004260280920581755 47498239506390421380872633)
        ·
          refine ⟨35623679629792816035654475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47498239506390421380872633 35623679629792816035654475)
          ·
            refine ⟨53435519444689224053481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35623679629792816035654475 53435519444689224053481713)
            ·
              refine ⟨40076639583516918040111285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53435519444689224053481713 40076639583516918040111285)
              ·
                refine ⟨3757184960954711066260433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40076639583516918040111285 3757184960954711066260433)
                ·
                  refine ⟨2817888720716033299695325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757184960954711066260433 2817888720716033299695325)
                  ·
                    refine ⟨1056708270268512487385747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817888720716033299695325 1056708270268512487385747)
                    ·
                      rfl

theorem cell22_3086898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_3086898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086898 prefixEnd_3086898 := by exact prefixLift 3086898
  have htrace : WordTrace (prefixWord ++ tailWord_3086898) baseStart_3086898 baseEnd_3086898 := by
    simpa [prefixWord, tailWord_3086898, baseEnd_3086898] using wordTrace_append hprefix tailTrace_3086898
  have hstable : (prefixWord ++ tailWord_3086898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086898).length < 2 ^ (prefixWord ++ tailWord_3086898).sum := by decide
  have hdescent : baseEnd_3086898 < baseStart_3086898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086949 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_3086949 : Nat := 118140960795 + 3086949 * 2 ^ 59
def prefixEnd_3086949 : Nat := 4983230072969 + 3 ^ 40 * 3086949 * 2
def baseEnd_3086949 : Nat := 1056725728610765354360591

theorem tailTrace_3086949 : CollatzResearch.WordTrace tailWord_3086949 prefixEnd_3086949 1056725728610765354360591 := by
  unfold tailWord_3086949
  simp only [CollatzResearch.WordTrace]
  refine ⟨112590279693518456761063901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75060186462345637840709267 112590279693518456761063901)
  ·
    refine ⟨42221354885069421285398963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112590279693518456761063901 42221354885069421285398963)
    ·
      refine ⟨63332032327604131928098445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42221354885069421285398963 63332032327604131928098445)
      ·
        refine ⟨23749512122851549473036917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63332032327604131928098445 23749512122851549473036917)
        ·
          refine ⟨2226516761517332763097211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23749512122851549473036917 2226516761517332763097211)
          ·
            refine ⟨3339775142275999144645817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226516761517332763097211 3339775142275999144645817)
            ·
              refine ⟨2504831356706999358484363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339775142275999144645817 2504831356706999358484363)
              ·
                refine ⟨3757247035060499037726545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504831356706999358484363 3757247035060499037726545)
                ·
                  refine ⟨2817935276295374278294909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757247035060499037726545 2817935276295374278294909)
                  ·
                    refine ⟨1056725728610765354360591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817935276295374278294909 1056725728610765354360591)
                    ·
                      rfl

theorem cell22_3086949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_3086949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086949 prefixEnd_3086949 := by exact prefixLift 3086949
  have htrace : WordTrace (prefixWord ++ tailWord_3086949) baseStart_3086949 baseEnd_3086949 := by
    simpa [prefixWord, tailWord_3086949, baseEnd_3086949] using wordTrace_append hprefix tailTrace_3086949
  have hstable : (prefixWord ++ tailWord_3086949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086949).length < 2 ^ (prefixWord ++ tailWord_3086949).sum := by decide
  have hdescent : baseEnd_3086949 < baseStart_3086949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086994 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3086994 : Nat := 118140960795 + 3086994 * 2 ^ 59
def prefixEnd_3086994 : Nat := 4983230072969 + 3 ^ 40 * 3086994 * 2
def baseEnd_3086994 : Nat := 1056741133030400236985453

theorem tailTrace_3086994 : CollatzResearch.WordTrace tailWord_3086994 prefixEnd_3086994 1056741133030400236985453 := by
  unfold tailWord_3086994
  simp only [CollatzResearch.WordTrace]
  refine ⟨28147980244588857361613009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75061280652236952964301357 28147980244588857361613009)
  ·
    refine ⟨21110985183441643021209757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28147980244588857361613009 21110985183441643021209757)
    ·
      refine ⟨7916619443790616132953659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21110985183441643021209757 7916619443790616132953659)
      ·
        refine ⟨11874929165685924199430489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7916619443790616132953659 11874929165685924199430489)
        ·
          refine ⟨8906196874264443149572867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11874929165685924199430489 8906196874264443149572867)
          ·
            refine ⟨13359295311396664724359301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8906196874264443149572867 13359295311396664724359301)
            ·
              refine ⟨2504867870886874635817369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13359295311396664724359301 2504867870886874635817369)
              ·
                refine ⟨1878650903165155976863027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504867870886874635817369 1878650903165155976863027)
                ·
                  refine ⟨2817976354747733965294541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878650903165155976863027 2817976354747733965294541)
                  ·
                    refine ⟨1056741133030400236985453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2817976354747733965294541 1056741133030400236985453)
                    ·
                      rfl

theorem cell22_3086994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3086994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3086994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3086994 prefixEnd_3086994 := by exact prefixLift 3086994
  have htrace : WordTrace (prefixWord ++ tailWord_3086994) baseStart_3086994 baseEnd_3086994 := by
    simpa [prefixWord, tailWord_3086994, baseEnd_3086994] using wordTrace_append hprefix tailTrace_3086994
  have hstable : (prefixWord ++ tailWord_3086994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086994).length < 2 ^ (prefixWord ++ tailWord_3086994).sum := by decide
  have hdescent : baseEnd_3086994 < baseStart_3086994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087001 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 6]
def baseStart_3087001 : Nat := 118140960795 + 3087001 * 2 ^ 59
def prefixEnd_3087001 : Nat := 4983230072969 + 3 ^ 40 * 3087001 * 2
def baseEnd_3087001 : Nat := 352247843091151517353477

theorem tailTrace_3087001 : CollatzResearch.WordTrace tailWord_3087001 prefixEnd_3087001 352247843091151517353477 := by
  unfold tailWord_3087001
  simp only [CollatzResearch.WordTrace]
  refine ⟨112592176289330069641956857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75061450859553379761304571 112592176289330069641956857)
  ·
    refine ⟨84444132216997552231467643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112592176289330069641956857 84444132216997552231467643)
    ·
      refine ⟨126666198325496328347201465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84444132216997552231467643 126666198325496328347201465)
      ·
        refine ⟨94999648744122246260401099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126666198325496328347201465 94999648744122246260401099)
        ·
          refine ⟨142499473116183369390601649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94999648744122246260401099 142499473116183369390601649)
          ·
            refine ⟨106874604837137527042951237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142499473116183369390601649 106874604837137527042951237)
            ·
              refine ⟨20038988406963286320553357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106874604837137527042951237 20038988406963286320553357)
              ·
                refine ⟨7514620652611232370207509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20038988406963286320553357 7514620652611232370207509)
                ·
                  refine ⟨352247843091151517353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7514620652611232370207509 352247843091151517353477)
                  ·
                    rfl

theorem cell22_3087001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_3087001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087001 prefixEnd_3087001 := by exact prefixLift 3087001
  have htrace : WordTrace (prefixWord ++ tailWord_3087001) baseStart_3087001 baseEnd_3087001 := by
    simpa [prefixWord, tailWord_3087001, baseEnd_3087001] using wordTrace_append hprefix tailTrace_3087001
  have hstable : (prefixWord ++ tailWord_3087001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087001).length < 2 ^ (prefixWord ++ tailWord_3087001).sum := by decide
  have hdescent : baseEnd_3087001 < baseStart_3087001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087033 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_3087033 : Nat := 118140960795 + 3087033 * 2 ^ 59
def prefixEnd_3087033 : Nat := 4983230072969 + 3 ^ 40 * 3087033 * 2
def baseEnd_3087033 : Nat := 1056754483527417135260333

theorem tailTrace_3087033 : CollatzResearch.WordTrace tailWord_3087033 prefixEnd_3087033 1056754483527417135260333 := by
  unfold tailWord_3087033
  simp only [CollatzResearch.WordTrace]
  refine ⟨112593343425214139107121753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75062228950142759404747835 112593343425214139107121753)
  ·
    refine ⟨84445007568910604330341315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112593343425214139107121753 84445007568910604330341315)
    ·
      refine ⟨126667511353365906495511973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84445007568910604330341315 126667511353365906495511973)
      ·
        refine ⟨23750158378756107467908495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126667511353365906495511973 23750158378756107467908495)
        ·
          refine ⟨35625237568134161201862743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23750158378756107467908495 35625237568134161201862743)
          ·
            refine ⟨53437856352201241802794115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35625237568134161201862743 53437856352201241802794115)
            ·
              refine ⟨80156784528301862704191173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53437856352201241802794115 80156784528301862704191173)
              ·
                refine ⟨15029397099056599257035845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80156784528301862704191173 15029397099056599257035845)
                ·
                  refine ⟨2818011956073112360694221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15029397099056599257035845 2818011956073112360694221)
                  ·
                    refine ⟨1056754483527417135260333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818011956073112360694221 1056754483527417135260333)
                    ·
                      rfl

theorem cell22_3087033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_3087033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087033 prefixEnd_3087033 := by exact prefixLift 3087033
  have htrace : WordTrace (prefixWord ++ tailWord_3087033) baseStart_3087033 baseEnd_3087033 := by
    simpa [prefixWord, tailWord_3087033, baseEnd_3087033] using wordTrace_append hprefix tailTrace_3087033
  have hstable : (prefixWord ++ tailWord_3087033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087033).length < 2 ^ (prefixWord ++ tailWord_3087033).sum := by decide
  have hdescent : baseEnd_3087033 < baseStart_3087033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087037 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_3087037 : Nat := 118140960795 + 3087037 * 2 ^ 59
def prefixEnd_3087037 : Nat := 4983230072969 + 3 ^ 40 * 3087037 * 2
def baseEnd_3087037 : Nat := 1056755852809162458160321

theorem tailTrace_3087037 : CollatzResearch.WordTrace tailWord_3087037 prefixEnd_3087037 1056755852809162458160321 := by
  unfold tailWord_3087037
  simp only [CollatzResearch.WordTrace]
  refine ⟨112593489317199647790267365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75062326211466431860178243 112593489317199647790267365)
  ·
    refine ⟨21111279246974933960675131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112593489317199647790267365 21111279246974933960675131)
    ·
      refine ⟨31666918870462400941012697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21111279246974933960675131 31666918870462400941012697)
      ·
        refine ⟨23750189152846800705759523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31666918870462400941012697 23750189152846800705759523)
        ·
          refine ⟨35625283729270201058639285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23750189152846800705759523 35625283729270201058639285)
          ·
            refine ⟨3339870349619081349247433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35625283729270201058639285 3339870349619081349247433)
            ·
              refine ⟨2504902762214311011935575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339870349619081349247433 2504902762214311011935575)
              ·
                refine ⟨3757354143321466517903363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504902762214311011935575 3757354143321466517903363)
                ·
                  refine ⟨5636031214982199776855045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757354143321466517903363 5636031214982199776855045)
                  ·
                    refine ⟨1056755852809162458160321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636031214982199776855045 1056755852809162458160321)
                    ·
                      rfl

theorem cell22_3087037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_3087037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087037 prefixEnd_3087037 := by exact prefixLift 3087037
  have htrace : WordTrace (prefixWord ++ tailWord_3087037) baseStart_3087037 baseEnd_3087037 := by
    simpa [prefixWord, tailWord_3087037, baseEnd_3087037] using wordTrace_append hprefix tailTrace_3087037
  have hstable : (prefixWord ++ tailWord_3087037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087037).length < 2 ^ (prefixWord ++ tailWord_3087037).sum := by decide
  have hdescent : baseEnd_3087037 < baseStart_3087037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087050 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3087050 : Nat := 118140960795 + 3087050 * 2 ^ 59
def prefixEnd_3087050 : Nat := 4983230072969 + 3 ^ 40 * 3087050 * 2
def baseEnd_3087050 : Nat := 1056760302974834757585281

theorem tailTrace_3087050 : CollatzResearch.WordTrace tailWord_3087050 prefixEnd_3087050 1056760302974834757585281 := by
  unfold tailWord_3087050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148490866538137752622651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75062642310768367340327069 28148490866538137752622651)
  ·
    refine ⟨42222736299807206628933977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28148490866538137752622651 42222736299807206628933977)
    ·
      refine ⟨31667052224855404971700483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42222736299807206628933977 31667052224855404971700483)
      ·
        refine ⟨47500578337283107457550725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31667052224855404971700483 47500578337283107457550725)
        ·
          refine ⟨8906358438240582648290761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47500578337283107457550725 8906358438240582648290761)
          ·
            refine ⟨6679768828680436986218071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8906358438240582648290761 6679768828680436986218071)
            ·
              refine ⟨10019653243020655479327107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679768828680436986218071 10019653243020655479327107)
              ·
                refine ⟨15029479864530983218990661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10019653243020655479327107 15029479864530983218990661)
                ·
                  refine ⟨2818027474599559353560749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15029479864530983218990661 2818027474599559353560749)
                  ·
                    refine ⟨1056760302974834757585281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818027474599559353560749 1056760302974834757585281)
                    ·
                      rfl

theorem cell22_3087050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3087050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087050 prefixEnd_3087050 := by exact prefixLift 3087050
  have htrace : WordTrace (prefixWord ++ tailWord_3087050) baseStart_3087050 baseEnd_3087050 := by
    simpa [prefixWord, tailWord_3087050, baseEnd_3087050] using wordTrace_append hprefix tailTrace_3087050
  have hstable : (prefixWord ++ tailWord_3087050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087050).length < 2 ^ (prefixWord ++ tailWord_3087050).sum := by decide
  have hdescent : baseEnd_3087050 < baseStart_3087050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087108 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3087108 : Nat := 118140960795 + 3087108 * 2 ^ 59
def prefixEnd_3087108 : Nat := 4983230072969 + 3 ^ 40 * 3087108 * 2
def baseEnd_3087108 : Nat := 352260052520047313211701

theorem tailTrace_3087108 : CollatzResearch.WordTrace tailWord_3087108 prefixEnd_3087108 352260052520047313211701 := by
  unfold tailWord_3087108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56298039449971213458050989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75064052599961617944067985 56298039449971213458050989)
  ·
    refine ⟨21111764793739205046769121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56298039449971213458050989 21111764793739205046769121)
    ·
      refine ⟨15833823595304403785076841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21111764793739205046769121 15833823595304403785076841)
      ·
        refine ⟨11875367696478302838807631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15833823595304403785076841 11875367696478302838807631)
        ·
          refine ⟨17813051544717454258211447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875367696478302838807631 17813051544717454258211447)
          ·
            refine ⟨26719577317076181387317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17813051544717454258211447 26719577317076181387317171)
            ·
              refine ⟨40079365975614272080975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26719577317076181387317171 40079365975614272080975757)
              ·
                refine ⟨15029762240855352030365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40079365975614272080975757 15029762240855352030365909)
                ·
                  refine ⟨352260052520047313211701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15029762240855352030365909 352260052520047313211701)
                  ·
                    rfl

theorem cell22_3087108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3087108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087108 prefixEnd_3087108 := by exact prefixLift 3087108
  have htrace : WordTrace (prefixWord ++ tailWord_3087108) baseStart_3087108 baseEnd_3087108 := by
    simpa [prefixWord, tailWord_3087108, baseEnd_3087108] using wordTrace_append hprefix tailTrace_3087108
  have hstable : (prefixWord ++ tailWord_3087108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087108).length < 2 ^ (prefixWord ++ tailWord_3087108).sum := by decide
  have hdescent : baseEnd_3087108 < baseStart_3087108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087112 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_3087112 : Nat := 118140960795 + 3087112 * 2 ^ 59
def prefixEnd_3087112 : Nat := 4983230072969 + 3 ^ 40 * 3087112 * 2
def baseEnd_3087112 : Nat := 1056781526841887262535091

theorem tailTrace_3087112 : CollatzResearch.WordTrace tailWord_3087112 prefixEnd_3087112 1056781526841887262535091 := by
  unfold tailWord_3087112
  simp only [CollatzResearch.WordTrace]
  refine ⟨56298112395963967799623795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75064149861285290399498393 56298112395963967799623795)
  ·
    refine ⟨84447168593945951699435693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56298112395963967799623795 84447168593945951699435693)
    ·
      refine ⟨31667688222729731887288385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84447168593945951699435693 31667688222729731887288385)
      ·
        refine ⟨23750766167047298915466289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31667688222729731887288385 23750766167047298915466289)
        ·
          refine ⟨17813074625285474186599717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23750766167047298915466289 17813074625285474186599717)
          ·
            refine ⟨3339951492241026409987447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17813074625285474186599717 3339951492241026409987447)
            ·
              refine ⟨5009927238361539614981171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339951492241026409987447 5009927238361539614981171)
              ·
                refine ⟨7514890857542309422471757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009927238361539614981171 7514890857542309422471757)
                ·
                  refine ⟨2818084071578366033426909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7514890857542309422471757 2818084071578366033426909)
                  ·
                    refine ⟨1056781526841887262535091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818084071578366033426909 1056781526841887262535091)
                    ·
                      rfl

theorem cell22_3087112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_3087112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087112 prefixEnd_3087112 := by exact prefixLift 3087112
  have htrace : WordTrace (prefixWord ++ tailWord_3087112) baseStart_3087112 baseEnd_3087112 := by
    simpa [prefixWord, tailWord_3087112, baseEnd_3087112] using wordTrace_append hprefix tailTrace_3087112
  have hstable : (prefixWord ++ tailWord_3087112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087112).length < 2 ^ (prefixWord ++ tailWord_3087112).sum := by decide
  have hdescent : baseEnd_3087112 < baseStart_3087112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
