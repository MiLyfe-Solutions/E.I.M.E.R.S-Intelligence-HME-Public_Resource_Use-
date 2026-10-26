import V185TrunkScan23Chunk0405

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2400878 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2400878 : Nat := 118140960795 + 2400878 * 2 ^ 59
def prefixEnd_2400878 : Nat := 4983230072969 + 3 ^ 40 * 2400878 * 2
def baseEnd_2400878 : Nat := 410934802268454262494523

theorem tailTrace_2400878 : CollatzResearch.WordTrace tailWord_2400878 prefixEnd_2400878 410934802268454262494523 := by
  unfold tailWord_2400878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10945901824504564770346411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58378143064024345441847525 10945901824504564770346411)
  ·
    refine ⟨16418852736756847155519617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10945901824504564770346411 16418852736756847155519617)
    ·
      refine ⟨12314139552567635366639713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16418852736756847155519617 12314139552567635366639713)
      ·
        refine ⟨9235604664425726524979785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12314139552567635366639713 9235604664425726524979785)
        ·
          refine ⟨6926703498319294893734839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9235604664425726524979785 6926703498319294893734839)
          ·
            refine ⟨10390055247478942340602259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6926703498319294893734839 10390055247478942340602259)
            ·
              refine ⟨15585082871218413510903389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390055247478942340602259 15585082871218413510903389)
              ·
                refine ⟨5844406076706905066588771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15585082871218413510903389 5844406076706905066588771)
                ·
                  refine ⟨8766609115060357599883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5844406076706905066588771 8766609115060357599883157)
                  ·
                    refine ⟨410934802268454262494523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8766609115060357599883157 410934802268454262494523)
                    ·
                      rfl

theorem cell23_2400878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2400878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400878 prefixEnd_2400878 := by exact prefixLift 2400878
  have htrace : WordTrace (prefixWord ++ tailWord_2400878) baseStart_2400878 baseEnd_2400878 := by
    simpa [prefixWord, tailWord_2400878, baseEnd_2400878] using wordTrace_append hprefix tailTrace_2400878
  have hstable : (prefixWord ++ tailWord_2400878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400878).length < 2 ^ (prefixWord ++ tailWord_2400878).sum := by decide
  have hdescent : baseEnd_2400878 < baseStart_2400878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2400942 : List Nat := [4, 1, 4, 1, 1, 3, 2, 7]
def baseStart_2400942 : Nat := 118140960795 + 2400942 * 2 ^ 59
def prefixEnd_2400942 : Nat := 4983230072969 + 3 ^ 40 * 2400942 * 2
def baseEnd_2400942 : Nat := 45660639613601871743825

theorem tailTrace_2400942 : CollatzResearch.WordTrace tailWord_2400942 prefixEnd_2400942 45660639613601871743825 := by
  unfold tailWord_2400942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10946193608475582136637635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58379699245203104728734053 10946193608475582136637635)
  ·
    refine ⟨16419290412713373204956453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10946193608475582136637635 16419290412713373204956453)
    ·
      refine ⟨3078616952383757475929335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16419290412713373204956453 3078616952383757475929335)
      ·
        refine ⟨4617925428575636213894003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078616952383757475929335 4617925428575636213894003)
        ·
          refine ⟨6926888142863454320841005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617925428575636213894003 6926888142863454320841005)
          ·
            refine ⟨2597583053573795370315377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6926888142863454320841005 2597583053573795370315377)
            ·
              refine ⟨1948187290180346527736533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597583053573795370315377 1948187290180346527736533)
              ·
                refine ⟨45660639613601871743825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1948187290180346527736533 45660639613601871743825)
                ·
                  rfl

theorem cell23_2400942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_2400942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2400942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2400942 prefixEnd_2400942 := by exact prefixLift 2400942
  have htrace : WordTrace (prefixWord ++ tailWord_2400942) baseStart_2400942 baseEnd_2400942 := by
    simpa [prefixWord, tailWord_2400942, baseEnd_2400942] using wordTrace_append hprefix tailTrace_2400942
  have hstable : (prefixWord ++ tailWord_2400942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2400942).length < 2 ^ (prefixWord ++ tailWord_2400942).sum := by decide
  have hdescent : baseEnd_2400942 < baseStart_2400942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2400942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401026 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_2401026 : Nat := 118140960795 + 2401026 * 2 ^ 59
def prefixEnd_2401026 : Nat := 4983230072969 + 3 ^ 40 * 2401026 * 2
def baseEnd_2401026 : Nat := 1232880401942228208432889

theorem tailTrace_2401026 : CollatzResearch.WordTrace tailWord_2401026 prefixEnd_2401026 1232880401942228208432889 := by
  unfold tailWord_2401026
  simp only [CollatzResearch.WordTrace]
  refine ⟨21893153149875084859789733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58381741733000226292772621 21893153149875084859789733)
  ·
    refine ⟨4104966215601578411210575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21893153149875084859789733 4104966215601578411210575)
    ·
      refine ⟨6157449323402367616815863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104966215601578411210575 6157449323402367616815863)
      ·
        refine ⟨9236173985103551425223795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157449323402367616815863 9236173985103551425223795)
        ·
          refine ⟨13854260977655327137835693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9236173985103551425223795 13854260977655327137835693)
          ·
            refine ⟨5195347866620747676688385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13854260977655327137835693 5195347866620747676688385)
            ·
              refine ⟨3896510899965560757516289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5195347866620747676688385 3896510899965560757516289)
              ·
                refine ⟨2922383174974170568137217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3896510899965560757516289 2922383174974170568137217)
                ·
                  refine ⟨2191787381230627926102913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922383174974170568137217 2191787381230627926102913)
                  ·
                    refine ⟨1643840535922970944577185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2191787381230627926102913 1643840535922970944577185)
                    ·
                      refine ⟨1232880401942228208432889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1643840535922970944577185 1232880401942228208432889)
                      ·
                        rfl

theorem cell23_2401026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_2401026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401026 prefixEnd_2401026 := by exact prefixLift 2401026
  have htrace : WordTrace (prefixWord ++ tailWord_2401026) baseStart_2401026 baseEnd_2401026 := by
    simpa [prefixWord, tailWord_2401026, baseEnd_2401026] using wordTrace_append hprefix tailTrace_2401026
  have hstable : (prefixWord ++ tailWord_2401026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401026).length < 2 ^ (prefixWord ++ tailWord_2401026).sum := by decide
  have hdescent : baseEnd_2401026 < baseStart_2401026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401032 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 5]
def baseStart_2401032 : Nat := 118140960795 + 2401032 * 2 ^ 59
def prefixEnd_2401032 : Nat := 4983230072969 + 3 ^ 40 * 2401032 * 2
def baseEnd_2401032 : Nat := 136987053647350576106429

theorem tailTrace_2401032 : CollatzResearch.WordTrace tailWord_2401032 prefixEnd_2401032 136987053647350576106429 := by
  unfold tailWord_2401032
  simp only [CollatzResearch.WordTrace]
  refine ⟨43786415718739301231938675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58381887624985734975918233 43786415718739301231938675)
  ·
    refine ⟨65679623578108951847908013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43786415718739301231938675 65679623578108951847908013)
    ·
      refine ⟨24629858841790856942965505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65679623578108951847908013 24629858841790856942965505)
      ·
        refine ⟨18472394131343142707224129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24629858841790856942965505 18472394131343142707224129)
        ·
          refine ⟨13854295598507357030418097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18472394131343142707224129 13854295598507357030418097)
          ·
            refine ⟨10390721698880517772813573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13854295598507357030418097 10390721698880517772813573)
            ·
              refine ⟨1948260318540097082402545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10390721698880517772813573 1948260318540097082402545)
              ·
                refine ⟨1461195238905072811801909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948260318540097082402545 1461195238905072811801909)
                ·
                  refine ⟨136987053647350576106429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1461195238905072811801909 136987053647350576106429)
                  ·
                    rfl

theorem cell23_2401032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 5].length) (baseStart_2401032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401032 prefixEnd_2401032 := by exact prefixLift 2401032
  have htrace : WordTrace (prefixWord ++ tailWord_2401032) baseStart_2401032 baseEnd_2401032 := by
    simpa [prefixWord, tailWord_2401032, baseEnd_2401032] using wordTrace_append hprefix tailTrace_2401032
  have hstable : (prefixWord ++ tailWord_2401032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401032).length < 2 ^ (prefixWord ++ tailWord_2401032).sum := by decide
  have hdescent : baseEnd_2401032 < baseStart_2401032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401048 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2401048 : Nat := 118140960795 + 2401048 * 2 ^ 59
def prefixEnd_2401048 : Nat := 4983230072969 + 3 ^ 40 * 2401048 * 2
def baseEnd_2401048 : Nat := 1232891698516627122357787

theorem tailTrace_2401048 : CollatzResearch.WordTrace tailWord_2401048 prefixEnd_2401048 1232891698516627122357787 := by
  unfold tailWord_2401048
  simp only [CollatzResearch.WordTrace]
  refine ⟨43786707502710318598229899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58382276670280424797639865 43786707502710318598229899)
  ·
    refine ⟨65680061254065477897344849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43786707502710318598229899 65680061254065477897344849)
    ·
      refine ⟨49260045940549108423008637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65680061254065477897344849 49260045940549108423008637)
      ·
        refine ⟨18472517227705915658628239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49260045940549108423008637 18472517227705915658628239)
        ·
          refine ⟨27708775841558873487942359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18472517227705915658628239 27708775841558873487942359)
          ·
            refine ⟨41563163762338310231913539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27708775841558873487942359 41563163762338310231913539)
            ·
              refine ⟨62344745643507465347870309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41563163762338310231913539 62344745643507465347870309)
              ·
                refine ⟨11689639808157649752725683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62344745643507465347870309 11689639808157649752725683)
                ·
                  refine ⟨17534459712236474629088525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11689639808157649752725683 17534459712236474629088525)
                  ·
                    refine ⟨6575422392088677985908197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17534459712236474629088525 6575422392088677985908197)
                    ·
                      refine ⟨1232891698516627122357787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6575422392088677985908197 1232891698516627122357787)
                      ·
                        rfl

theorem cell23_2401048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2401048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401048 prefixEnd_2401048 := by exact prefixLift 2401048
  have htrace : WordTrace (prefixWord ++ tailWord_2401048) baseStart_2401048 baseEnd_2401048 := by
    simpa [prefixWord, tailWord_2401048, baseEnd_2401048] using wordTrace_append hprefix tailTrace_2401048
  have hstable : (prefixWord ++ tailWord_2401048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401048).length < 2 ^ (prefixWord ++ tailWord_2401048).sum := by decide
  have hdescent : baseEnd_2401048 < baseStart_2401048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401115 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 3]
def baseStart_2401115 : Nat := 118140960795 + 2401115 * 2 ^ 59
def prefixEnd_2401115 : Nat := 4983230072969 + 3 ^ 40 * 2401115 * 2
def baseEnd_2401115 : Nat := 1232926101720478360219979

theorem tailTrace_2401115 : CollatzResearch.WordTrace tailWord_2401115 prefixEnd_2401115 1232926101720478360219979 := by
  unfold tailWord_2401115
  simp only [CollatzResearch.WordTrace]
  refine ⟨87575858696177907639148799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58383905797451938426099199 87575858696177907639148799)
  ·
    refine ⟨131363788044266861458723199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87575858696177907639148799 131363788044266861458723199)
    ·
      refine ⟨197045682066400292188084799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131363788044266861458723199 197045682066400292188084799)
      ·
        refine ⟨295568523099600438282127199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197045682066400292188084799 295568523099600438282127199)
        ·
          refine ⟨443352784649400657423190799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295568523099600438282127199 443352784649400657423190799)
          ·
            refine ⟨665029176974100986134786199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443352784649400657423190799 665029176974100986134786199)
            ·
              refine ⟨997543765461151479202179299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665029176974100986134786199 997543765461151479202179299)
              ·
                refine ⟨1496315648191727218803268949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997543765461151479202179299 1496315648191727218803268949)
                ·
                  refine ⟨2191868625280850418168851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 1496315648191727218803268949 2191868625280850418168851)
                  ·
                    refine ⟨3287802937921275627253277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191868625280850418168851 3287802937921275627253277)
                    ·
                      refine ⟨1232926101720478360219979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3287802937921275627253277 1232926101720478360219979)
                      ·
                        rfl

theorem cell23_2401115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 3].length) (baseStart_2401115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401115 prefixEnd_2401115 := by exact prefixLift 2401115
  have htrace : WordTrace (prefixWord ++ tailWord_2401115) baseStart_2401115 baseEnd_2401115 := by
    simpa [prefixWord, tailWord_2401115, baseEnd_2401115] using wordTrace_append hprefix tailTrace_2401115
  have hstable : (prefixWord ++ tailWord_2401115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401115).length < 2 ^ (prefixWord ++ tailWord_2401115).sum := by decide
  have hdescent : baseEnd_2401115 < baseStart_2401115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401149 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_2401149 : Nat := 118140960795 + 2401149 * 2 ^ 59
def prefixEnd_2401149 : Nat := 4983230072969 + 3 ^ 40 * 2401149 * 2
def baseEnd_2401149 : Nat := 1232943560062731227194823

theorem tailTrace_2401149 : CollatzResearch.WordTrace tailWord_2401149 prefixEnd_2401149 1232943560062731227194823 := by
  unfold tailWord_2401149
  simp only [CollatzResearch.WordTrace]
  refine ⟨87577098778054731445886501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58384732518703154297257667 87577098778054731445886501)
  ·
    refine ⟨16420706020885262146103719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87577098778054731445886501 16420706020885262146103719)
    ·
      refine ⟨24631059031327893219155579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16420706020885262146103719 24631059031327893219155579)
      ·
        refine ⟨36946588546991839828733369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24631059031327893219155579 36946588546991839828733369)
        ·
          refine ⟨27709941410243879871550027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36946588546991839828733369 27709941410243879871550027)
          ·
            refine ⟨41564912115365819807325041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27709941410243879871550027 41564912115365819807325041)
            ·
              refine ⟨31173684086524364855493781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41564912115365819807325041 31173684086524364855493781)
              ·
                refine ⟨1461266441555829602601271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31173684086524364855493781 1461266441555829602601271)
                ·
                  refine ⟨2191899662333744403901907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461266441555829602601271 2191899662333744403901907)
                  ·
                    refine ⟨3287849493500616605852861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191899662333744403901907 3287849493500616605852861)
                    ·
                      refine ⟨1232943560062731227194823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3287849493500616605852861 1232943560062731227194823)
                      ·
                        rfl

theorem cell23_2401149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_2401149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401149 prefixEnd_2401149 := by exact prefixLift 2401149
  have htrace : WordTrace (prefixWord ++ tailWord_2401149) baseStart_2401149 baseEnd_2401149 := by
    simpa [prefixWord, tailWord_2401149, baseEnd_2401149] using wordTrace_append hprefix tailTrace_2401149
  have hstable : (prefixWord ++ tailWord_2401149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401149).length < 2 ^ (prefixWord ++ tailWord_2401149).sum := by decide
  have hdescent : baseEnd_2401149 < baseStart_2401149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401155 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4]
def baseStart_2401155 : Nat := 118140960795 + 2401155 * 2 ^ 59
def prefixEnd_2401155 : Nat := 4983230072969 + 3 ^ 40 * 2401155 * 2
def baseEnd_2401155 : Nat := 1232946640946658203719795

theorem tailTrace_2401155 : CollatzResearch.WordTrace tailWord_2401155 prefixEnd_2401155 1232946640946658203719795 := by
  unfold tailWord_2401155
  simp only [CollatzResearch.WordTrace]
  refine ⟨87577317616032994470604919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58384878410688662980403279 87577317616032994470604919)
  ·
    refine ⟨131365976424049491705907379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87577317616032994470604919 131365976424049491705907379)
    ·
      refine ⟨197048964636074237558861069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131365976424049491705907379 197048964636074237558861069)
      ·
        refine ⟨73893361738527839084572901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197048964636074237558861069 73893361738527839084572901)
        ·
          refine ⟨13855005325973969828357419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73893361738527839084572901 13855005325973969828357419)
          ·
            refine ⟨20782507988960954742536129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13855005325973969828357419 20782507988960954742536129)
            ·
              refine ⟨15586880991720716056902097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20782507988960954742536129 15586880991720716056902097)
              ·
                refine ⟨11690160743790537042676573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15586880991720716056902097 11690160743790537042676573)
                ·
                  refine ⟨4383810278921451391003715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11690160743790537042676573 4383810278921451391003715)
                  ·
                    refine ⟨6575715418382177086505573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4383810278921451391003715 6575715418382177086505573)
                    ·
                      refine ⟨1232946640946658203719795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6575715418382177086505573 1232946640946658203719795)
                      ·
                        rfl

theorem cell23_2401155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_2401155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401155 prefixEnd_2401155 := by exact prefixLift 2401155
  have htrace : WordTrace (prefixWord ++ tailWord_2401155) baseStart_2401155 baseEnd_2401155 := by
    simpa [prefixWord, tailWord_2401155, baseEnd_2401155] using wordTrace_append hprefix tailTrace_2401155
  have hstable : (prefixWord ++ tailWord_2401155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401155).length < 2 ^ (prefixWord ++ tailWord_2401155).sum := by decide
  have hdescent : baseEnd_2401155 < baseStart_2401155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2401168 : Nat := 118140960795 + 2401168 * 2 ^ 59
def prefixEnd_2401168 : Nat := 4983230072969 + 3 ^ 40 * 2401168 * 2
def baseEnd_2401168 : Nat := 1232953316195166652857235

theorem tailTrace_2401168 : CollatzResearch.WordTrace tailWord_2401168 prefixEnd_2401168 1232953316195166652857235 := by
  unfold tailWord_2401168
  simp only [CollatzResearch.WordTrace]
  refine ⟨43788895882492948845414079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58385194509990598460552105 43788895882492948845414079)
  ·
    refine ⟨65683343823739423268121119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43788895882492948845414079 65683343823739423268121119)
    ·
      refine ⟨98525015735609134902181679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65683343823739423268121119 98525015735609134902181679)
      ·
        refine ⟨147787523603413702353272519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98525015735609134902181679 147787523603413702353272519)
        ·
          refine ⟨221681285405120553529908779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147787523603413702353272519 221681285405120553529908779)
          ·
            refine ⟨332521928107680830294863169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221681285405120553529908779 332521928107680830294863169)
            ·
              refine ⟨249391446080760622721147377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332521928107680830294863169 249391446080760622721147377)
              ·
                refine ⟨187043584560570467040860533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249391446080760622721147377 187043584560570467040860533)
                ·
                  refine ⟨17535336052553481285080675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187043584560570467040860533 17535336052553481285080675)
                  ·
                    refine ⟨26303004078830221927621013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17535336052553481285080675 26303004078830221927621013)
                    ·
                      refine ⟨1232953316195166652857235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26303004078830221927621013 1232953316195166652857235)
                      ·
                        rfl

theorem cell23_2401168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2401168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401168 prefixEnd_2401168 := by exact prefixLift 2401168
  have htrace : WordTrace (prefixWord ++ tailWord_2401168) baseStart_2401168 baseEnd_2401168 := by
    simpa [prefixWord, tailWord_2401168, baseEnd_2401168] using wordTrace_append hprefix tailTrace_2401168
  have hstable : (prefixWord ++ tailWord_2401168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401168).length < 2 ^ (prefixWord ++ tailWord_2401168).sum := by decide
  have hdescent : baseEnd_2401168 < baseStart_2401168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401172 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2401172 : Nat := 118140960795 + 2401172 * 2 ^ 59
def prefixEnd_2401172 : Nat := 4983230072969 + 3 ^ 40 * 2401172 * 2
def baseEnd_2401172 : Nat := 1232955370117784637207217

theorem tailTrace_2401172 : CollatzResearch.WordTrace tailWord_2401172 prefixEnd_2401172 1232955370117784637207217 := by
  unfold tailWord_2401172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43788968828485703186986885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58385291771314270915982513 43788968828485703186986885)
  ·
    refine ⟨8210431655341069347560041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43788968828485703186986885 8210431655341069347560041)
    ·
      refine ⟨6157823741505802010670031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8210431655341069347560041 6157823741505802010670031)
      ·
        refine ⟨9236735612258703016005047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157823741505802010670031 9236735612258703016005047)
        ·
          refine ⟨13855103418388054524007571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9236735612258703016005047 13855103418388054524007571)
          ·
            refine ⟨20782655127582081786011357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13855103418388054524007571 20782655127582081786011357)
            ·
              refine ⟨7793495672843280669754259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20782655127582081786011357 7793495672843280669754259)
              ·
                refine ⟨11690243509264921004631389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793495672843280669754259 11690243509264921004631389)
                ·
                  refine ⟨4383841315974345376736771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11690243509264921004631389 4383841315974345376736771)
                  ·
                    refine ⟨6575761973961518065105157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4383841315974345376736771 6575761973961518065105157)
                    ·
                      refine ⟨1232955370117784637207217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6575761973961518065105157 1232955370117784637207217)
                      ·
                        rfl

theorem cell23_2401172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2401172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401172 prefixEnd_2401172 := by exact prefixLift 2401172
  have htrace : WordTrace (prefixWord ++ tailWord_2401172) baseStart_2401172 baseEnd_2401172 := by
    simpa [prefixWord, tailWord_2401172, baseEnd_2401172] using wordTrace_append hprefix tailTrace_2401172
  have hstable : (prefixWord ++ tailWord_2401172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401172).length < 2 ^ (prefixWord ++ tailWord_2401172).sum := by decide
  have hdescent : baseEnd_2401172 < baseStart_2401172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401285 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 7]
def baseStart_2401285 : Nat := 118140960795 + 2401285 * 2 ^ 59
def prefixEnd_2401285 : Nat := 4983230072969 + 3 ^ 40 * 2401285 * 2
def baseEnd_2401285 : Nat := 137001488159082521677133

theorem tailTrace_2401285 : CollatzResearch.WordTrace tailWord_2401285 prefixEnd_2401285 137001488159082521677133 := by
  unfold tailWord_2401285
  simp only [CollatzResearch.WordTrace]
  refine ⟨87582059105562026672837309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58388039403708017781891539 87582059105562026672837309)
  ·
    refine ⟨32843272164585760002313991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87582059105562026672837309 32843272164585760002313991)
    ·
      refine ⟨49264908246878640003470987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32843272164585760002313991 49264908246878640003470987)
      ·
        refine ⟨73897362370317960005206481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49264908246878640003470987 73897362370317960005206481)
        ·
          refine ⟨55423021777738470003904861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73897362370317960005206481 55423021777738470003904861)
          ·
            refine ⟨20783633166651926251464323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55423021777738470003904861 20783633166651926251464323)
            ·
              refine ⟨31175449749977889377196485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20783633166651926251464323 31175449749977889377196485)
              ·
                refine ⟨5845396828120854258224341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31175449749977889377196485 5845396828120854258224341)
                ·
                  refine ⟨137001488159082521677133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5845396828120854258224341 137001488159082521677133)
                  ·
                    rfl

theorem cell23_2401285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_2401285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401285 prefixEnd_2401285 := by exact prefixLift 2401285
  have htrace : WordTrace (prefixWord ++ tailWord_2401285) baseStart_2401285 baseEnd_2401285 := by
    simpa [prefixWord, tailWord_2401285, baseEnd_2401285] using wordTrace_append hprefix tailTrace_2401285
  have hstable : (prefixWord ++ tailWord_2401285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401285).length < 2 ^ (prefixWord ++ tailWord_2401285).sum := by decide
  have hdescent : baseEnd_2401285 < baseStart_2401285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401319 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 7]
def baseStart_2401319 : Nat := 118140960795 + 2401319 * 2 ^ 59
def prefixEnd_2401319 : Nat := 4983230072969 + 3 ^ 40 * 2401319 * 2
def baseEnd_2401319 : Nat := 137003427974888395785449

theorem tailTrace_2401319 : CollatzResearch.WordTrace tailWord_2401319 prefixEnd_2401319 137003427974888395785449 := by
  unfold tailWord_2401319
  simp only [CollatzResearch.WordTrace]
  refine ⟨87583299187438850479575011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58388866124959233653050007 87583299187438850479575011)
  ·
    refine ⟨131374948781158275719362517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87583299187438850479575011 131374948781158275719362517)
    ·
      refine ⟨3079100362058397087172559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131374948781158275719362517 3079100362058397087172559)
      ·
        refine ⟨4618650543087595630758839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079100362058397087172559 4618650543087595630758839)
        ·
          refine ⟨6927975814631393446138259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618650543087595630758839 6927975814631393446138259)
          ·
            refine ⟨10391963721947090169207389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927975814631393446138259 10391963721947090169207389)
            ·
              refine ⟨3896986395730158813452771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10391963721947090169207389 3896986395730158813452771)
              ·
                refine ⟨5845479593595238220179157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896986395730158813452771 5845479593595238220179157)
                ·
                  refine ⟨137003427974888395785449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5845479593595238220179157 137003427974888395785449)
                  ·
                    rfl

theorem cell23_2401319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 7].length) (baseStart_2401319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401319 prefixEnd_2401319 := by exact prefixLift 2401319
  have htrace : WordTrace (prefixWord ++ tailWord_2401319) baseStart_2401319 baseEnd_2401319 := by
    simpa [prefixWord, tailWord_2401319, baseEnd_2401319] using wordTrace_append hprefix tailTrace_2401319
  have hstable : (prefixWord ++ tailWord_2401319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401319).length < 2 ^ (prefixWord ++ tailWord_2401319).sum := by decide
  have hdescent : baseEnd_2401319 < baseStart_2401319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401355 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_2401355 : Nat := 118140960795 + 2401355 * 2 ^ 59
def prefixEnd_2401355 : Nat := 4983230072969 + 3 ^ 40 * 2401355 * 2
def baseEnd_2401355 : Nat := 1233049337077557421218875

theorem tailTrace_2401355 : CollatzResearch.WordTrace tailWord_2401355 prefixEnd_2401355 1233049337077557421218875 := by
  unfold tailWord_2401355
  simp only [CollatzResearch.WordTrace]
  refine ⟨87584612215308428627885519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58389741476872285751923679 87584612215308428627885519)
  ·
    refine ⟨131376918322962642941828279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87584612215308428627885519 131376918322962642941828279)
    ·
      refine ⟨197065377484443964412742419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131376918322962642941828279 197065377484443964412742419)
      ·
        refine ⟨295598066226665946619113629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197065377484443964412742419 295598066226665946619113629)
        ·
          refine ⟨110849274834999729982167611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295598066226665946619113629 110849274834999729982167611)
          ·
            refine ⟨166273912252499594973251417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110849274834999729982167611 166273912252499594973251417)
            ·
              refine ⟨124705434189374696229938563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166273912252499594973251417 124705434189374696229938563)
              ·
                refine ⟨187058151284062044344907845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124705434189374696229938563 187058151284062044344907845)
                ·
                  refine ⟨35073403365761633314670221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187058151284062044344907845 35073403365761633314670221)
                  ·
                    refine ⟨13152526262160612493001333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35073403365761633314670221 13152526262160612493001333)
                    ·
                      refine ⟨1233049337077557421218875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13152526262160612493001333 1233049337077557421218875)
                      ·
                        rfl

theorem cell23_2401355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_2401355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401355 prefixEnd_2401355 := by exact prefixLift 2401355
  have htrace : WordTrace (prefixWord ++ tailWord_2401355) baseStart_2401355 baseEnd_2401355 := by
    simpa [prefixWord, tailWord_2401355, baseEnd_2401355] using wordTrace_append hprefix tailTrace_2401355
  have hstable : (prefixWord ++ tailWord_2401355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401355).length < 2 ^ (prefixWord ++ tailWord_2401355).sum := by decide
  have hdescent : baseEnd_2401355 < baseStart_2401355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401372 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2401372 : Nat := 118140960795 + 2401372 * 2 ^ 59
def prefixEnd_2401372 : Nat := 4983230072969 + 3 ^ 40 * 2401372 * 2
def baseEnd_2401372 : Nat := 1233058066248683854706297

theorem tailTrace_2401372 : CollatzResearch.WordTrace tailWord_2401372 prefixEnd_2401372 1233058066248683854706297 := by
  unfold tailWord_2401372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792616128123420265627185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58390154837497893687502913 43792616128123420265627185)
  ·
    refine ⟨32844462096092565199220389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43792616128123420265627185 32844462096092565199220389)
    ·
      refine ⟨6158336643017355974853823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32844462096092565199220389 6158336643017355974853823)
      ·
        refine ⟨9237504964526033962280735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158336643017355974853823 9237504964526033962280735)
        ·
          refine ⟨13856257446789050943421103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237504964526033962280735 13856257446789050943421103)
          ·
            refine ⟨20784386170183576415131655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13856257446789050943421103 20784386170183576415131655)
            ·
              refine ⟨31176579255275364622697483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20784386170183576415131655 31176579255275364622697483)
              ·
                refine ⟨46764868882913046934046225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31176579255275364622697483 46764868882913046934046225)
                ·
                  refine ⟨35073651662184785200534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46764868882913046934046225 35073651662184785200534669)
                  ·
                    refine ⟨13152619373319294450200501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35073651662184785200534669 13152619373319294450200501)
                    ·
                      refine ⟨1233058066248683854706297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13152619373319294450200501 1233058066248683854706297)
                      ·
                        rfl

theorem cell23_2401372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2401372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401372 prefixEnd_2401372 := by exact prefixLift 2401372
  have htrace : WordTrace (prefixWord ++ tailWord_2401372) baseStart_2401372 baseEnd_2401372 := by
    simpa [prefixWord, tailWord_2401372, baseEnd_2401372] using wordTrace_append hprefix tailTrace_2401372
  have hstable : (prefixWord ++ tailWord_2401372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401372).length < 2 ^ (prefixWord ++ tailWord_2401372).sum := by decide
  have hdescent : baseEnd_2401372 < baseStart_2401372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401386 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_2401386 : Nat := 118140960795 + 2401386 * 2 ^ 59
def prefixEnd_2401386 : Nat := 4983230072969 + 3 ^ 40 * 2401386 * 2
def baseEnd_2401386 : Nat := 1233065254977846799931233

theorem tailTrace_2401386 : CollatzResearch.WordTrace tailWord_2401386 prefixEnd_2401386 1233065254977846799931233 := by
  unfold tailWord_2401386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21896435719549030230566003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58390495252130747281509341 21896435719549030230566003)
  ·
    refine ⟨32844653579323545345849005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21896435719549030230566003 32844653579323545345849005)
    ·
      refine ⟨12316745092246329504693377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32844653579323545345849005 12316745092246329504693377)
      ·
        refine ⟨9237558819184747128520033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12316745092246329504693377 9237558819184747128520033)
        ·
          refine ⟨6928169114388560346390025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9237558819184747128520033 6928169114388560346390025)
          ·
            refine ⟨5196126835791420259792519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6928169114388560346390025 5196126835791420259792519)
            ·
              refine ⟨7794190253687130389688779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5196126835791420259792519 7794190253687130389688779)
              ·
                refine ⟨11691285380530695584533169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794190253687130389688779 11691285380530695584533169)
                ·
                  refine ⟨8768464035398021688399877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11691285380530695584533169 8768464035398021688399877)
                  ·
                    refine ⟨1644087006637129066574977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8768464035398021688399877 1644087006637129066574977)
                    ·
                      refine ⟨1233065254977846799931233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644087006637129066574977 1233065254977846799931233)
                      ·
                        rfl

theorem cell23_2401386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_2401386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401386 prefixEnd_2401386 := by exact prefixLift 2401386
  have htrace : WordTrace (prefixWord ++ tailWord_2401386) baseStart_2401386 baseEnd_2401386 := by
    simpa [prefixWord, tailWord_2401386, baseEnd_2401386] using wordTrace_append hprefix tailTrace_2401386
  have hstable : (prefixWord ++ tailWord_2401386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401386).length < 2 ^ (prefixWord ++ tailWord_2401386).sum := by decide
  have hdescent : baseEnd_2401386 < baseStart_2401386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401392 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 6]
def baseStart_2401392 : Nat := 118140960795 + 2401392 * 2 ^ 59
def prefixEnd_2401392 : Nat := 4983230072969 + 3 ^ 40 * 2401392 * 2
def baseEnd_2401392 : Nat := 137007592873530419606245

theorem tailTrace_2401392 : CollatzResearch.WordTrace tailWord_2401392 prefixEnd_2401392 137007592873530419606245 := by
  unfold tailWord_2401392
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792980858087191973491215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58390641144116255964654953 43792980858087191973491215)
  ·
    refine ⟨65689471287130787960236823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43792980858087191973491215 65689471287130787960236823)
    ·
      refine ⟨98534206930696181940355235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65689471287130787960236823 98534206930696181940355235)
      ·
        refine ⟨147801310396044272910532853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98534206930696181940355235 147801310396044272910532853)
        ·
          refine ⟨13856372849629150585362455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147801310396044272910532853 13856372849629150585362455)
          ·
            refine ⟨20784559274443725878043683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13856372849629150585362455 20784559274443725878043683)
            ·
              refine ⟨31176838911665588817065525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20784559274443725878043683 31176838911665588817065525)
              ·
                refine ⟨2922828647968648951599893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31176838911665588817065525 2922828647968648951599893)
                ·
                  refine ⟨137007592873530419606245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2922828647968648951599893 137007592873530419606245)
                  ·
                    rfl

theorem cell23_2401392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_2401392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401392 prefixEnd_2401392 := by exact prefixLift 2401392
  have htrace : WordTrace (prefixWord ++ tailWord_2401392) baseStart_2401392 baseEnd_2401392 := by
    simpa [prefixWord, tailWord_2401392, baseEnd_2401392] using wordTrace_append hprefix tailTrace_2401392
  have hstable : (prefixWord ++ tailWord_2401392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401392).length < 2 ^ (prefixWord ++ tailWord_2401392).sum := by decide
  have hdescent : baseEnd_2401392 < baseStart_2401392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401413 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_2401413 : Nat := 118140960795 + 2401413 * 2 ^ 59
def prefixEnd_2401413 : Nat := 4983230072969 + 3 ^ 40 * 2401413 * 2
def baseEnd_2401413 : Nat := 411026372985172731431203

theorem tailTrace_2401413 : CollatzResearch.WordTrace tailWord_2401413 prefixEnd_2401413 411026372985172731431203 := by
  unfold tailWord_2401413
  simp only [CollatzResearch.WordTrace]
  refine ⟨87586727649098304533496893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58391151766065536355664595 87586727649098304533496893)
  ·
    refine ⟨32845022868411864200061335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87586727649098304533496893 32845022868411864200061335)
    ·
      refine ⟨49267534302617796300092003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32845022868411864200061335 49267534302617796300092003)
      ·
        refine ⟨73901301453926694450138005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49267534302617796300092003 73901301453926694450138005)
        ·
          refine ⟨3464123505652813802350219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73901301453926694450138005 3464123505652813802350219)
          ·
            refine ⟨5196185258479220703525329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464123505652813802350219 5196185258479220703525329)
            ·
              refine ⟨3897138943859415527643997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196185258479220703525329 3897138943859415527643997)
              ·
                refine ⟨1461427103947280822866499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3897138943859415527643997 1461427103947280822866499)
                ·
                  refine ⟨2192140655920921234299749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461427103947280822866499 2192140655920921234299749)
                  ·
                    refine ⟨411026372985172731431203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192140655920921234299749 411026372985172731431203)
                    ·
                      rfl

theorem cell23_2401413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_2401413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401413 prefixEnd_2401413 := by exact prefixLift 2401413
  have htrace : WordTrace (prefixWord ++ tailWord_2401413) baseStart_2401413 baseEnd_2401413 := by
    simpa [prefixWord, tailWord_2401413, baseEnd_2401413] using wordTrace_append hprefix tailTrace_2401413
  have hstable : (prefixWord ++ tailWord_2401413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401413).length < 2 ^ (prefixWord ++ tailWord_2401413).sum := by decide
  have hdescent : baseEnd_2401413 < baseStart_2401413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401426 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 6]
def baseStart_2401426 : Nat := 118140960795 + 2401426 * 2 ^ 59
def prefixEnd_2401426 : Nat := 4983230072969 + 3 ^ 40 * 2401426 * 2
def baseEnd_2401426 : Nat := 137009532689336293714561

theorem tailTrace_2401426 : CollatzResearch.WordTrace tailWord_2401426 prefixEnd_2401426 137009532689336293714561 := by
  unfold tailWord_2401426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21896800449512801938430033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58391467865367471835813421 21896800449512801938430033)
  ·
    refine ⟨16422600337134601453822525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21896800449512801938430033 16422600337134601453822525)
    ·
      refine ⟨6158475126425475545183447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16422600337134601453822525 6158475126425475545183447)
      ·
        refine ⟨9237712689638213317775171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158475126425475545183447 9237712689638213317775171)
        ·
          refine ⟨13856569034457319976662757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237712689638213317775171 13856569034457319976662757)
          ·
            refine ⟨2598106693960747495624267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13856569034457319976662757 2598106693960747495624267)
            ·
              refine ⟨3897160040941121243436401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598106693960747495624267 3897160040941121243436401)
              ·
                refine ⟨2922870030705840932577301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897160040941121243436401 2922870030705840932577301)
                ·
                  refine ⟨137009532689336293714561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2922870030705840932577301 137009532689336293714561)
                  ·
                    rfl

theorem cell23_2401426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_2401426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401426 prefixEnd_2401426 := by exact prefixLift 2401426
  have htrace : WordTrace (prefixWord ++ tailWord_2401426) baseStart_2401426 baseEnd_2401426 := by
    simpa [prefixWord, tailWord_2401426, baseEnd_2401426] using wordTrace_append hprefix tailTrace_2401426
  have hstable : (prefixWord ++ tailWord_2401426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401426).length < 2 ^ (prefixWord ++ tailWord_2401426).sum := by decide
  have hdescent : baseEnd_2401426 < baseStart_2401426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401436 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2401436 : Nat := 118140960795 + 2401436 * 2 ^ 59
def prefixEnd_2401436 : Nat := 4983230072969 + 3 ^ 40 * 2401436 * 2
def baseEnd_2401436 : Nat := 1233090929010571604306003

theorem tailTrace_2401436 : CollatzResearch.WordTrace tailWord_2401436 prefixEnd_2401436 1233090929010571604306003 := by
  unfold tailWord_2401436
  simp only [CollatzResearch.WordTrace]
  refine ⟨43793783264007489730792081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58391711018676652974389441 43793783264007489730792081)
  ·
    refine ⟨32845337448005617298094061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43793783264007489730792081 32845337448005617298094061)
    ·
      refine ⟨12317001543002106486785273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32845337448005617298094061 12317001543002106486785273)
      ·
        refine ⟨9237751157251579865088955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12317001543002106486785273 9237751157251579865088955)
        ·
          refine ⟨13856626735877369797633433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237751157251579865088955 13856626735877369797633433)
          ·
            refine ⟨10392470051908027348225075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13856626735877369797633433 10392470051908027348225075)
            ·
              refine ⟨15588705077862041022337613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10392470051908027348225075 15588705077862041022337613)
              ·
                refine ⟨5845764404198265383376605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15588705077862041022337613 5845764404198265383376605)
                ·
                  refine ⟨2192161651574349518766227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5845764404198265383376605 2192161651574349518766227)
                  ·
                    refine ⟨3288242477361524278149341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192161651574349518766227 3288242477361524278149341)
                    ·
                      refine ⟨1233090929010571604306003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288242477361524278149341 1233090929010571604306003)
                      ·
                        rfl

theorem cell23_2401436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2401436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401436 prefixEnd_2401436 := by exact prefixLift 2401436
  have htrace : WordTrace (prefixWord ++ tailWord_2401436) baseStart_2401436 baseEnd_2401436 := by
    simpa [prefixWord, tailWord_2401436, baseEnd_2401436] using wordTrace_append hprefix tailTrace_2401436
  have hstable : (prefixWord ++ tailWord_2401436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401436).length < 2 ^ (prefixWord ++ tailWord_2401436).sum := by decide
  have hdescent : baseEnd_2401436 < baseStart_2401436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401452 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_2401452 : Nat := 118140960795 + 2401452 * 2 ^ 59
def prefixEnd_2401452 : Nat := 4983230072969 + 3 ^ 40 * 2401452 * 2
def baseEnd_2401452 : Nat := 411033048233681180568643

theorem tailTrace_2401452 : CollatzResearch.WordTrace tailWord_2401452 prefixEnd_2401452 411033048233681180568643 := by
  unfold tailWord_2401452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43794075047978507097083305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58392100063971342796111073 43794075047978507097083305)
  ·
    refine ⟨32845556285983880322812479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43794075047978507097083305 32845556285983880322812479)
    ·
      refine ⟨49268334428975820484218719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32845556285983880322812479 49268334428975820484218719)
      ·
        refine ⟨73902501643463730726328079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49268334428975820484218719 73902501643463730726328079)
        ·
          refine ⟨110853752465195596089492119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73902501643463730726328079 110853752465195596089492119)
          ·
            refine ⟨166280628697793394134238179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110853752465195596089492119 166280628697793394134238179)
            ·
              refine ⟨249420943046690091201357269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166280628697793394134238179 249420943046690091201357269)
              ·
                refine ⟨5845803352656799012531811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249420943046690091201357269 5845803352656799012531811)
                ·
                  refine ⟨8768705028985198518797717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845803352656799012531811 8768705028985198518797717)
                  ·
                    refine ⟨411033048233681180568643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8768705028985198518797717 411033048233681180568643)
                    ·
                      rfl

theorem cell23_2401452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_2401452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401452 prefixEnd_2401452 := by exact prefixLift 2401452
  have htrace : WordTrace (prefixWord ++ tailWord_2401452) baseStart_2401452 baseEnd_2401452 := by
    simpa [prefixWord, tailWord_2401452, baseEnd_2401452] using wordTrace_append hprefix tailTrace_2401452
  have hstable : (prefixWord ++ tailWord_2401452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401452).length < 2 ^ (prefixWord ++ tailWord_2401452).sum := by decide
  have hdescent : baseEnd_2401452 < baseStart_2401452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401459 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 4]
def baseStart_2401459 : Nat := 118140960795 + 2401459 * 2 ^ 59
def prefixEnd_2401459 : Nat := 4983230072969 + 3 ^ 40 * 2401459 * 2
def baseEnd_2401459 : Nat := 1233102739065625014318397

theorem tailTrace_2401459 : CollatzResearch.WordTrace tailWord_2401459 prefixEnd_2401459 1233102739065625014318397 := by
  unfold tailWord_2401459
  simp only [CollatzResearch.WordTrace]
  refine ⟨87588405406931654389671431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58392270271287769593114287 87588405406931654389671431)
  ·
    refine ⟨131382608110397481584507147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87588405406931654389671431 131382608110397481584507147)
    ·
      refine ⟨197073912165596222376760721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131382608110397481584507147 197073912165596222376760721)
      ·
        refine ⟨147805434124197166782570541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197073912165596222376760721 147805434124197166782570541)
        ·
          refine ⟨55427037796573937543463953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147805434124197166782570541 55427037796573937543463953)
          ·
            refine ⟨41570278347430453157597965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55427037796573937543463953 41570278347430453157597965)
            ·
              refine ⟨15588854380286419934099237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41570278347430453157597965 15588854380286419934099237)
              ·
                refine ⟨2922910196303703737643607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15588854380286419934099237 2922910196303703737643607)
                ·
                  refine ⟨4384365294455555606465411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922910196303703737643607 4384365294455555606465411)
                  ·
                    refine ⟨6576547941683333409698117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4384365294455555606465411 6576547941683333409698117)
                    ·
                      refine ⟨1233102739065625014318397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6576547941683333409698117 1233102739065625014318397)
                      ·
                        rfl

theorem cell23_2401459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_2401459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401459 prefixEnd_2401459 := by exact prefixLift 2401459
  have htrace : WordTrace (prefixWord ++ tailWord_2401459) baseStart_2401459 baseEnd_2401459 := by
    simpa [prefixWord, tailWord_2401459, baseEnd_2401459] using wordTrace_append hprefix tailTrace_2401459
  have hstable : (prefixWord ++ tailWord_2401459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401459).length < 2 ^ (prefixWord ++ tailWord_2401459).sum := by decide
  have hdescent : baseEnd_2401459 < baseStart_2401459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401469 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_2401469 : Nat := 118140960795 + 2401469 * 2 ^ 59
def prefixEnd_2401469 : Nat := 4983230072969 + 3 ^ 40 * 2401469 * 2
def baseEnd_2401469 : Nat := 411035957957389991731117

theorem tailTrace_2401469 : CollatzResearch.WordTrace tailWord_2401469 prefixEnd_2401469 411035957957389991731117 := by
  unfold tailWord_2401469
  simp only [CollatzResearch.WordTrace]
  refine ⟨87588770136895426097535461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58392513424596950731690307 87588770136895426097535461)
  ·
    refine ⟨16422894400667892393287899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87588770136895426097535461 16422894400667892393287899)
    ·
      refine ⟨24634341601001838589931849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16422894400667892393287899 24634341601001838589931849)
      ·
        refine ⟨18475756200751378942448887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24634341601001838589931849 18475756200751378942448887)
        ·
          refine ⟨27713634301127068413673331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18475756200751378942448887 27713634301127068413673331)
          ·
            refine ⟨41570451451690602620509997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27713634301127068413673331 41570451451690602620509997)
            ·
              refine ⟨15588919294383975982691249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41570451451690602620509997 15588919294383975982691249)
              ·
                refine ⟨11691689470787981987018437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15588919294383975982691249 11691689470787981987018437)
                ·
                  refine ⟨2192191775772746622565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11691689470787981987018437 2192191775772746622565957)
                  ·
                    refine ⟨411035957957389991731117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192191775772746622565957 411035957957389991731117)
                    ·
                      rfl

theorem cell23_2401469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_2401469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401469 prefixEnd_2401469 := by exact prefixLift 2401469
  have htrace : WordTrace (prefixWord ++ tailWord_2401469) baseStart_2401469 baseEnd_2401469 := by
    simpa [prefixWord, tailWord_2401469, baseEnd_2401469] using wordTrace_append hprefix tailTrace_2401469
  have hstable : (prefixWord ++ tailWord_2401469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401469).length < 2 ^ (prefixWord ++ tailWord_2401469).sum := by decide
  have hdescent : baseEnd_2401469 < baseStart_2401469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401470 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_2401470 : Nat := 118140960795 + 2401470 * 2 ^ 59
def prefixEnd_2401470 : Nat := 4983230072969 + 3 ^ 40 * 2401470 * 2
def baseEnd_2401470 : Nat := 1233108387352824471280847

theorem tailTrace_2401470 : CollatzResearch.WordTrace tailWord_2401470 prefixEnd_2401470 1233108387352824471280847 := by
  unfold tailWord_2401470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948600826236475408540233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58392537739927868845547909 10948600826236475408540233)
  ·
    refine ⟨8211450619677356556405175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10948600826236475408540233 8211450619677356556405175)
    ·
      refine ⟨12317175929516034834607763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211450619677356556405175 12317175929516034834607763)
      ·
        refine ⟨18475763894274052251911645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12317175929516034834607763 18475763894274052251911645)
        ·
          refine ⟨6928411460352769594466867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18475763894274052251911645 6928411460352769594466867)
          ·
            refine ⟨10392617190529154391700301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928411460352769594466867 10392617190529154391700301)
            ·
              refine ⟨3897231446448432896887613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10392617190529154391700301 3897231446448432896887613)
              ·
                refine ⟨1461461792418162336332855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3897231446448432896887613 1461461792418162336332855)
                ·
                  refine ⟨2192192688627243504499283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461461792418162336332855 2192192688627243504499283)
                  ·
                    refine ⟨3288289032940865256748925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192192688627243504499283 3288289032940865256748925)
                    ·
                      refine ⟨1233108387352824471280847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288289032940865256748925 1233108387352824471280847)
                      ·
                        rfl

theorem cell23_2401470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_2401470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401470 prefixEnd_2401470 := by exact prefixLift 2401470
  have htrace : WordTrace (prefixWord ++ tailWord_2401470) baseStart_2401470 baseEnd_2401470 := by
    simpa [prefixWord, tailWord_2401470, baseEnd_2401470] using wordTrace_append hprefix tailTrace_2401470
  have hstable : (prefixWord ++ tailWord_2401470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401470).length < 2 ^ (prefixWord ++ tailWord_2401470).sum := by decide
  have hdescent : baseEnd_2401470 < baseStart_2401470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401482 : List Nat := [3, 1, 2, 1, 3, 2, 11]
def baseStart_2401482 : Nat := 118140960795 + 2401482 * 2 ^ 59
def prefixEnd_2401482 : Nat := 4983230072969 + 3 ^ 40 * 2401482 * 2
def baseEnd_2401482 : Nat := 15223636408897264497911

theorem tailTrace_2401482 : CollatzResearch.WordTrace tailWord_2401482 prefixEnd_2401482 15223636408897264497911 := by
  unfold tailWord_2401482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897311071462082329439675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58392829523898886211839133 21897311071462082329439675)
  ·
    refine ⟨32845966607193123494159513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21897311071462082329439675 32845966607193123494159513)
    ·
      refine ⟨24634474955394842620619635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32845966607193123494159513 24634474955394842620619635)
      ·
        refine ⟨36951712433092263930929453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24634474955394842620619635 36951712433092263930929453)
        ·
          refine ⟨13856892162409598974098545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36951712433092263930929453 13856892162409598974098545)
          ·
            refine ⟨10392669121807199230573909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13856892162409598974098545 10392669121807199230573909)
            ·
              refine ⟨15223636408897264497911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10392669121807199230573909 15223636408897264497911)
              ·
                rfl

theorem cell23_2401482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 11].length) (baseStart_2401482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401482 prefixEnd_2401482 := by exact prefixLift 2401482
  have htrace : WordTrace (prefixWord ++ tailWord_2401482) baseStart_2401482 baseEnd_2401482 := by
    simpa [prefixWord, tailWord_2401482, baseEnd_2401482] using wordTrace_append hprefix tailTrace_2401482
  have hstable : (prefixWord ++ tailWord_2401482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401482).length < 2 ^ (prefixWord ++ tailWord_2401482).sum := by decide
  have hdescent : baseEnd_2401482 < baseStart_2401482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401544 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_2401544 : Nat := 118140960795 + 2401544 * 2 ^ 59
def prefixEnd_2401544 : Nat := 4983230072969 + 3 ^ 40 * 2401544 * 2
def baseEnd_2401544 : Nat := 1233146384921257181755507

theorem tailTrace_2401544 : CollatzResearch.WordTrace tailWord_2401544 prefixEnd_2401544 1233146384921257181755507 := by
  unfold tailWord_2401544
  simp only [CollatzResearch.WordTrace]
  refine ⟨43795752805811856953257843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58394337074415809271010457 43795752805811856953257843)
  ·
    refine ⟨65693629208717785429886765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43795752805811856953257843 65693629208717785429886765)
    ·
      refine ⟨24635110953269169536207537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65693629208717785429886765 24635110953269169536207537)
      ·
        refine ⟨18476333214951877152155653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24635110953269169536207537 18476333214951877152155653)
        ·
          refine ⟨3464312477803476966029185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18476333214951877152155653 3464312477803476966029185)
          ·
            refine ⟨2598234358352607724521889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3464312477803476966029185 2598234358352607724521889)
            ·
              refine ⟨1948675768764455793391417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2598234358352607724521889 1948675768764455793391417)
              ·
                refine ⟨1461506826573341845043563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948675768764455793391417 1461506826573341845043563)
                ·
                  refine ⟨2192260239860012767565345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461506826573341845043563 2192260239860012767565345)
                  ·
                    refine ⟨1644195179895009575674009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192260239860012767565345 1644195179895009575674009)
                    ·
                      refine ⟨1233146384921257181755507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644195179895009575674009 1233146384921257181755507)
                      ·
                        rfl

theorem cell23_2401544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_2401544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401544 prefixEnd_2401544 := by exact prefixLift 2401544
  have htrace : WordTrace (prefixWord ++ tailWord_2401544) baseStart_2401544 baseEnd_2401544 := by
    simpa [prefixWord, tailWord_2401544, baseEnd_2401544] using wordTrace_append hprefix tailTrace_2401544
  have hstable : (prefixWord ++ tailWord_2401544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401544).length < 2 ^ (prefixWord ++ tailWord_2401544).sum := by decide
  have hdescent : baseEnd_2401544 < baseStart_2401544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401559 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 2, 6]
def baseStart_2401559 : Nat := 118140960795 + 2401559 * 2 ^ 59
def prefixEnd_2401559 : Nat := 4983230072969 + 3 ^ 40 * 2401559 * 2
def baseEnd_2401559 : Nat := 411051362377024874355979

theorem tailTrace_2401559 : CollatzResearch.WordTrace tailWord_2401559 prefixEnd_2401559 411051362377024874355979 := by
  unfold tailWord_2401559
  simp only [CollatzResearch.WordTrace]
  refine ⟨87592052706569371468311731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58394701804379580978874487 87592052706569371468311731)
  ·
    refine ⟨131388079059854057202467597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87592052706569371468311731 131388079059854057202467597)
    ·
      refine ⟨49270529647445271450925349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131388079059854057202467597 49270529647445271450925349)
      ·
        refine ⟨9238224308895988397048503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49270529647445271450925349 9238224308895988397048503)
        ·
          refine ⟨13857336463343982595572755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9238224308895988397048503 13857336463343982595572755)
          ·
            refine ⟨20786004695015973893359133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13857336463343982595572755 20786004695015973893359133)
            ·
              refine ⟨7794751760630990210009675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20786004695015973893359133 7794751760630990210009675)
              ·
                refine ⟨11692127640946485315014513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794751760630990210009675 11692127640946485315014513)
                ·
                  refine ⟨8769095730709863986260885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11692127640946485315014513 8769095730709863986260885)
                  ·
                    refine ⟨411051362377024874355979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8769095730709863986260885 411051362377024874355979)
                    ·
                      rfl

theorem cell23_2401559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_2401559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401559 prefixEnd_2401559 := by exact prefixLift 2401559
  have htrace : WordTrace (prefixWord ++ tailWord_2401559) baseStart_2401559 baseEnd_2401559 := by
    simpa [prefixWord, tailWord_2401559, baseEnd_2401559] using wordTrace_append hprefix tailTrace_2401559
  have hstable : (prefixWord ++ tailWord_2401559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401559).length < 2 ^ (prefixWord ++ tailWord_2401559).sum := by decide
  have hdescent : baseEnd_2401559 < baseStart_2401559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401569 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2401569 : Nat := 118140960795 + 2401569 * 2 ^ 59
def prefixEnd_2401569 : Nat := 4983230072969 + 3 ^ 40 * 2401569 * 2
def baseEnd_2401569 : Nat := 1233159221937619583942891

theorem tailTrace_2401569 : CollatzResearch.WordTrace tailWord_2401569 prefixEnd_2401569 1233159221937619583942891 := by
  unfold tailWord_2401569
  simp only [CollatzResearch.WordTrace]
  refine ⟨87592417436533143176175761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58394944957688762117450507 87592417436533143176175761)
  ·
    refine ⟨65694313077399857382131821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87592417436533143176175761 65694313077399857382131821)
    ·
      refine ⟨24635367404024946518299433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65694313077399857382131821 24635367404024946518299433)
      ·
        refine ⟨18476525553018709888724575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24635367404024946518299433 18476525553018709888724575)
        ·
          refine ⟨27714788329528064833086863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18476525553018709888724575 27714788329528064833086863)
          ·
            refine ⟨41572182494292097249630295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27714788329528064833086863 41572182494292097249630295)
            ·
              refine ⟨62358273741438145874445443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41572182494292097249630295 62358273741438145874445443)
              ·
                refine ⟨93537410612157218811668165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62358273741438145874445443 93537410612157218811668165)
                ·
                  refine ⟨17538264489779478527187781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93537410612157218811668165 17538264489779478527187781)
                  ·
                    refine ⟨3288424591833652223847709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17538264489779478527187781 3288424591833652223847709)
                    ·
                      refine ⟨1233159221937619583942891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288424591833652223847709 1233159221937619583942891)
                      ·
                        rfl

theorem cell23_2401569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2401569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401569 prefixEnd_2401569 := by exact prefixLift 2401569
  have htrace : WordTrace (prefixWord ++ tailWord_2401569) baseStart_2401569 baseEnd_2401569 := by
    simpa [prefixWord, tailWord_2401569, baseEnd_2401569] using wordTrace_append hprefix tailTrace_2401569
  have hstable : (prefixWord ++ tailWord_2401569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401569).length < 2 ^ (prefixWord ++ tailWord_2401569).sum := by decide
  have hdescent : baseEnd_2401569 < baseStart_2401569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401626 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_2401626 : Nat := 118140960795 + 2401626 * 2 ^ 59
def prefixEnd_2401626 : Nat := 4983230072969 + 3 ^ 40 * 2401626 * 2
def baseEnd_2401626 : Nat := 1233188490334925860930129

theorem tailTrace_2401626 : CollatzResearch.WordTrace tailWord_2401626 prefixEnd_2401626 1233188490334925860930129 := by
  unfold tailWord_2401626
  simp only [CollatzResearch.WordTrace]
  refine ⟨21898624099331660477750183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58396330931551094607333821 21898624099331660477750183)
  ·
    refine ⟨32847936148997490716625275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21898624099331660477750183 32847936148997490716625275)
    ·
      refine ⟨49271904223496236074937913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32847936148997490716625275 49271904223496236074937913)
      ·
        refine ⟨36953928167622177056203435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49271904223496236074937913 36953928167622177056203435)
        ·
          refine ⟨55430892251433265584305153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36953928167622177056203435 55430892251433265584305153)
          ·
            refine ⟨41573169188574949188228865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55430892251433265584305153 41573169188574949188228865)
            ·
              refine ⟨31179876891431211891171649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41573169188574949188228865 31179876891431211891171649)
              ·
                refine ⟨23384907668573408918378737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31179876891431211891171649 23384907668573408918378737)
                ·
                  refine ⟨17538680751430056688784053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23384907668573408918378737 17538680751430056688784053)
                  ·
                    refine ⟨1644251320446567814573505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17538680751430056688784053 1644251320446567814573505)
                    ·
                      refine ⟨1233188490334925860930129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644251320446567814573505 1233188490334925860930129)
                      ·
                        rfl

theorem cell23_2401626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_2401626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401626 prefixEnd_2401626 := by exact prefixLift 2401626
  have htrace : WordTrace (prefixWord ++ tailWord_2401626) baseStart_2401626 baseEnd_2401626 := by
    simpa [prefixWord, tailWord_2401626, baseEnd_2401626] using wordTrace_append hprefix tailTrace_2401626
  have hstable : (prefixWord ++ tailWord_2401626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401626).length < 2 ^ (prefixWord ++ tailWord_2401626).sum := by decide
  have hdescent : baseEnd_2401626 < baseStart_2401626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401640 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 5]
def baseStart_2401640 : Nat := 118140960795 + 2401640 * 2 ^ 59
def prefixEnd_2401640 : Nat := 4983230072969 + 3 ^ 40 * 2401640 * 2
def baseEnd_2401640 : Nat := 137021742118232089572785

theorem tailTrace_2401640 : CollatzResearch.WordTrace tailWord_2401640 prefixEnd_2401640 137021742118232089572785 := by
  unfold tailWord_2401640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43797503509637961151005187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58396671346183948201340249 43797503509637961151005187)
  ·
    refine ⟨65696255264456941726507781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43797503509637961151005187 65696255264456941726507781)
    ·
      refine ⟨12318047862085676573720209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65696255264456941726507781 12318047862085676573720209)
      ·
        refine ⟨9238535896564257430290157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12318047862085676573720209 9238535896564257430290157)
        ·
          refine ⟨3464450961211596536358809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9238535896564257430290157 3464450961211596536358809)
          ·
            refine ⟨2598338220908697402269107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3464450961211596536358809 2598338220908697402269107)
            ·
              refine ⟨3897507331363046103403661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598338220908697402269107 3897507331363046103403661)
              ·
                refine ⟨1461565249261142288776373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3897507331363046103403661 1461565249261142288776373)
                ·
                  refine ⟨137021742118232089572785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1461565249261142288776373 137021742118232089572785)
                  ·
                    rfl

theorem cell23_2401640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 5].length) (baseStart_2401640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401640 prefixEnd_2401640 := by exact prefixLift 2401640
  have htrace : WordTrace (prefixWord ++ tailWord_2401640) baseStart_2401640 baseEnd_2401640 := by
    simpa [prefixWord, tailWord_2401640, baseEnd_2401640] using wordTrace_append hprefix tailTrace_2401640
  have hstable : (prefixWord ++ tailWord_2401640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401640).length < 2 ^ (prefixWord ++ tailWord_2401640).sum := by decide
  have hdescent : baseEnd_2401640 < baseStart_2401640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401653 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2401653 : Nat := 118140960795 + 2401653 * 2 ^ 59
def prefixEnd_2401653 : Nat := 4983230072969 + 3 ^ 40 * 2401653 * 2
def baseEnd_2401653 : Nat := 411067451437532418430835

theorem tailTrace_2401653 : CollatzResearch.WordTrace tailWord_2401653 prefixEnd_2401653 411067451437532418430835 := by
  unfold tailWord_2401653
  simp only [CollatzResearch.WordTrace]
  refine ⟨87595481168228825522233613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58396987445485883681489075 87595481168228825522233613)
  ·
    refine ⟨32848305438085809570837605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87595481168228825522233613 32848305438085809570837605)
    ·
      refine ⟨6159057269641089294532051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32848305438085809570837605 6159057269641089294532051)
      ·
        refine ⟨9238585904461633941798077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159057269641089294532051 9238585904461633941798077)
        ·
          refine ⟨3464469714173112728174279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9238585904461633941798077 3464469714173112728174279)
          ·
            refine ⟨5196704571259669092261419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464469714173112728174279 5196704571259669092261419)
            ·
              refine ⟨7795056856889503638392129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5196704571259669092261419 7795056856889503638392129)
              ·
                refine ⟨5846292642667127728794097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795056856889503638392129 5846292642667127728794097)
                ·
                  refine ⟨4384719482000345796595573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5846292642667127728794097 4384719482000345796595573)
                  ·
                    refine ⟨411067451437532418430835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4384719482000345796595573 411067451437532418430835)
                    ·
                      rfl

theorem cell23_2401653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2401653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401653 prefixEnd_2401653 := by exact prefixLift 2401653
  have htrace : WordTrace (prefixWord ++ tailWord_2401653) baseStart_2401653 baseEnd_2401653 := by
    simpa [prefixWord, tailWord_2401653, baseEnd_2401653] using wordTrace_append hprefix tailTrace_2401653
  have hstable : (prefixWord ++ tailWord_2401653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401653).length < 2 ^ (prefixWord ++ tailWord_2401653).sum := by decide
  have hdescent : baseEnd_2401653 < baseStart_2401653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401669 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2401669 : Nat := 118140960795 + 2401669 * 2 ^ 59
def prefixEnd_2401669 : Nat := 4983230072969 + 3 ^ 40 * 2401669 * 2
def baseEnd_2401669 : Nat := 1233210570003069192692431

theorem tailTrace_2401669 : CollatzResearch.WordTrace tailWord_2401669 prefixEnd_2401669 1233210570003069192692431 := by
  unfold tailWord_2401669
  simp only [CollatzResearch.WordTrace]
  refine ⟨87596064736170860254816061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58397376490780573503210707 87596064736170860254816061)
  ·
    refine ⟨32848524276064072595556023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87596064736170860254816061 32848524276064072595556023)
    ·
      refine ⟨49272786414096108893334035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32848524276064072595556023 49272786414096108893334035)
      ·
        refine ⟨73909179621144163340001053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49272786414096108893334035 73909179621144163340001053)
        ·
          refine ⟨27715942357929061252500395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73909179621144163340001053 27715942357929061252500395)
          ·
            refine ⟨41573913536893591878750593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27715942357929061252500395 41573913536893591878750593)
            ·
              refine ⟨31180435152670193909062945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41573913536893591878750593 31180435152670193909062945)
              ·
                refine ⟨23385326364502645431797209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31180435152670193909062945 23385326364502645431797209)
                ·
                  refine ⟨17538994773376984073847907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23385326364502645431797209 17538994773376984073847907)
                  ·
                    refine ⟨26308492160065476110771861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17538994773376984073847907 26308492160065476110771861)
                    ·
                      refine ⟨1233210570003069192692431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26308492160065476110771861 1233210570003069192692431)
                      ·
                        rfl

theorem cell23_2401669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2401669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401669 prefixEnd_2401669 := by exact prefixLift 2401669
  have htrace : WordTrace (prefixWord ++ tailWord_2401669) baseStart_2401669 baseEnd_2401669 := by
    simpa [prefixWord, tailWord_2401669, baseEnd_2401669] using wordTrace_append hprefix tailTrace_2401669
  have hstable : (prefixWord ++ tailWord_2401669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401669).length < 2 ^ (prefixWord ++ tailWord_2401669).sum := by decide
  have hdescent : baseEnd_2401669 < baseStart_2401669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401676 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2401676 : Nat := 118140960795 + 2401676 * 2 ^ 59
def prefixEnd_2401676 : Nat := 4983230072969 + 3 ^ 40 * 2401676 * 2
def baseEnd_2401676 : Nat := 1233214164367650665304899

theorem tailTrace_2401676 : CollatzResearch.WordTrace tailWord_2401676 prefixEnd_2401676 1233214164367650665304899 := by
  unfold tailWord_2401676
  simp only [CollatzResearch.WordTrace]
  refine ⟨43798160023572750225160441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58397546698097000300213921 43798160023572750225160441)
  ·
    refine ⟨32848620017679562668870331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43798160023572750225160441 32848620017679562668870331)
    ·
      refine ⟨49272930026519344003305497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32848620017679562668870331 49272930026519344003305497)
      ·
        refine ⟨36954697519889508002479123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49272930026519344003305497 36954697519889508002479123)
        ·
          refine ⟨55432046279834262003718685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36954697519889508002479123 55432046279834262003718685)
          ·
            refine ⟨20787017354937848251394507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55432046279834262003718685 20787017354937848251394507)
            ·
              refine ⟨31180526032406772377091761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20787017354937848251394507 31180526032406772377091761)
              ·
                refine ⟨23385394524305079282818821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31180526032406772377091761 23385394524305079282818821)
                ·
                  refine ⟨4384761473307202365528529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23385394524305079282818821 4384761473307202365528529)
                  ·
                    refine ⟨3288571104980401774146397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4384761473307202365528529 3288571104980401774146397)
                    ·
                      refine ⟨1233214164367650665304899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288571104980401774146397 1233214164367650665304899)
                      ·
                        rfl

theorem cell23_2401676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2401676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401676 prefixEnd_2401676 := by exact prefixLift 2401676
  have htrace : WordTrace (prefixWord ++ tailWord_2401676) baseStart_2401676 baseEnd_2401676 := by
    simpa [prefixWord, tailWord_2401676, baseEnd_2401676] using wordTrace_append hprefix tailTrace_2401676
  have hstable : (prefixWord ++ tailWord_2401676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401676).length < 2 ^ (prefixWord ++ tailWord_2401676).sum := by decide
  have hdescent : baseEnd_2401676 < baseStart_2401676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401693 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2401693 : Nat := 118140960795 + 2401693 * 2 ^ 59
def prefixEnd_2401693 : Nat := 4983230072969 + 3 ^ 40 * 2401693 * 2
def baseEnd_2401693 : Nat := 1233222893538777098792321

theorem tailTrace_2401693 : CollatzResearch.WordTrace tailWord_2401693 prefixEnd_2401693 1233222893538777098792321 := by
  unfold tailWord_2401693
  simp only [CollatzResearch.WordTrace]
  refine ⟨87596940088083912353689733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58397960058722608235793155 87596940088083912353689733)
  ·
    refine ⟨16424426266515733566316825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87596940088083912353689733 16424426266515733566316825)
    ·
      refine ⟨12318319699886800174737619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16424426266515733566316825 12318319699886800174737619)
      ·
        refine ⟨18477479549830200262106429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12318319699886800174737619 18477479549830200262106429)
        ·
          refine ⟨6929054831186325098289911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18477479549830200262106429 6929054831186325098289911)
          ·
            refine ⟨10393582246779487647434867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929054831186325098289911 10393582246779487647434867)
            ·
              refine ⟨15590373370169231471152301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10393582246779487647434867 15590373370169231471152301)
              ·
                refine ⟨5846390013813461801682113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15590373370169231471152301 5846390013813461801682113)
                ·
                  refine ⟨4384792510360096351261585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5846390013813461801682113 4384792510360096351261585)
                  ·
                    refine ⟨3288594382770072263446189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4384792510360096351261585 3288594382770072263446189)
                    ·
                      refine ⟨1233222893538777098792321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288594382770072263446189 1233222893538777098792321)
                      ·
                        rfl

theorem cell23_2401693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2401693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401693 prefixEnd_2401693 := by exact prefixLift 2401693
  have htrace : WordTrace (prefixWord ++ tailWord_2401693) baseStart_2401693 baseEnd_2401693 := by
    simpa [prefixWord, tailWord_2401693, baseEnd_2401693] using wordTrace_append hprefix tailTrace_2401693
  have hstable : (prefixWord ++ tailWord_2401693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401693).length < 2 ^ (prefixWord ++ tailWord_2401693).sum := by decide
  have hdescent : baseEnd_2401693 < baseStart_2401693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401717 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2401717 : Nat := 118140960795 + 2401717 * 2 ^ 59
def prefixEnd_2401717 : Nat := 4983230072969 + 3 ^ 40 * 2401717 * 2
def baseEnd_2401717 : Nat := 411078405691495001630737

theorem tailTrace_2401717 : CollatzResearch.WordTrace tailWord_2401717 prefixEnd_2401717 411078405691495001630737 := by
  unfold tailWord_2401717
  simp only [CollatzResearch.WordTrace]
  refine ⟨87597815439996964452563405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58398543626664642968375603 87597815439996964452563405)
  ·
    refine ⟨32849180789998861669711277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87597815439996964452563405 32849180789998861669711277)
    ·
      refine ⟨12318442796249573126141729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32849180789998861669711277 12318442796249573126141729)
      ·
        refine ⟨9238832097187179844606297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12318442796249573126141729 9238832097187179844606297)
        ·
          refine ⟨6929124072890384883454723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9238832097187179844606297 6929124072890384883454723)
          ·
            refine ⟨10393686109335577325182085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929124072890384883454723 10393686109335577325182085)
            ·
              refine ⟨1948816145500420748471641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10393686109335577325182085 1948816145500420748471641)
              ·
                refine ⟨1461612109125315561353731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948816145500420748471641 1461612109125315561353731)
                ·
                  refine ⟨2192418163687973342030597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461612109125315561353731 2192418163687973342030597)
                  ·
                    refine ⟨411078405691495001630737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192418163687973342030597 411078405691495001630737)
                    ·
                      rfl

theorem cell23_2401717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2401717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401717 prefixEnd_2401717 := by exact prefixLift 2401717
  have htrace : WordTrace (prefixWord ++ tailWord_2401717) baseStart_2401717 baseEnd_2401717 := by
    simpa [prefixWord, tailWord_2401717, baseEnd_2401717] using wordTrace_append hprefix tailTrace_2401717
  have hstable : (prefixWord ++ tailWord_2401717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401717).length < 2 ^ (prefixWord ++ tailWord_2401717).sum := by decide
  have hdescent : baseEnd_2401717 < baseStart_2401717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401740 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2401740 : Nat := 118140960795 + 2401740 * 2 ^ 59
def prefixEnd_2401740 : Nat := 4983230072969 + 3 ^ 40 * 2401740 * 2
def baseEnd_2401740 : Nat := 1233247027129538414904605

theorem tailTrace_2401740 : CollatzResearch.WordTrace tailWord_2401740 prefixEnd_2401740 1233247027129538414904605 := by
  unfold tailWord_2401740
  simp only [CollatzResearch.WordTrace]
  refine ⟨43799327159456819690325337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58399102879275759587100449 43799327159456819690325337)
  ·
    refine ⟨32849495369592614767744003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43799327159456819690325337 32849495369592614767744003)
    ·
      refine ⟨49274243054388922151616005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32849495369592614767744003 49274243054388922151616005)
      ·
        refine ⟨9238920572697922903428001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49274243054388922151616005 9238920572697922903428001)
        ·
          refine ⟨6929190429523442177571001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9238920572697922903428001 6929190429523442177571001)
          ·
            refine ⟨5196892822142581633178251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929190429523442177571001 5196892822142581633178251)
            ·
              refine ⟨7795339233213872449767377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5196892822142581633178251 7795339233213872449767377)
              ·
                refine ⟨5846504424910404337325533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795339233213872449767377 5846504424910404337325533)
                ·
                  refine ⟨2192439159341401626497075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5846504424910404337325533 2192439159341401626497075)
                  ·
                    refine ⟨3288658739012102439745613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192439159341401626497075 3288658739012102439745613)
                    ·
                      refine ⟨1233247027129538414904605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288658739012102439745613 1233247027129538414904605)
                      ·
                        rfl

theorem cell23_2401740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2401740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401740 prefixEnd_2401740 := by exact prefixLift 2401740
  have htrace : WordTrace (prefixWord ++ tailWord_2401740) baseStart_2401740 baseEnd_2401740 := by
    simpa [prefixWord, tailWord_2401740, baseEnd_2401740] using wordTrace_append hprefix tailTrace_2401740
  have hstable : (prefixWord ++ tailWord_2401740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401740).length < 2 ^ (prefixWord ++ tailWord_2401740).sum := by decide
  have hdescent : baseEnd_2401740 < baseStart_2401740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401757 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_2401757 : Nat := 118140960795 + 2401757 * 2 ^ 59
def prefixEnd_2401757 : Nat := 4983230072969 + 3 ^ 40 * 2401757 * 2
def baseEnd_2401757 : Nat := 1233255756300664848392027

theorem tailTrace_2401757 : CollatzResearch.WordTrace tailWord_2401757 prefixEnd_2401757 1233255756300664848392027 := by
  unfold tailWord_2401757
  simp only [CollatzResearch.WordTrace]
  refine ⟨87599274359852051284019525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58399516239901367522679683 87599274359852051284019525)
  ·
    refine ⟨16424863942472259615753661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87599274359852051284019525 16424863942472259615753661)
    ·
      refine ⟨6159323978427097355907623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16424863942472259615753661 6159323978427097355907623)
      ·
        refine ⟨9238985967640646033861435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159323978427097355907623 9238985967640646033861435)
        ·
          refine ⟨13858478951460969050792153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9238985967640646033861435 13858478951460969050792153)
          ·
            refine ⟨10393859213595726788094115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13858478951460969050792153 10393859213595726788094115)
            ·
              refine ⟨15590788820393590182141173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10393859213595726788094115 15590788820393590182141173)
              ·
                refine ⟨1461636451911899079575735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15590788820393590182141173 1461636451911899079575735)
                ·
                  refine ⟨2192454677867848619363603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461636451911899079575735 2192454677867848619363603)
                  ·
                    refine ⟨3288682016801772929045405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192454677867848619363603 3288682016801772929045405)
                    ·
                      refine ⟨1233255756300664848392027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288682016801772929045405 1233255756300664848392027)
                      ·
                        rfl

theorem cell23_2401757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_2401757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401757 prefixEnd_2401757 := by exact prefixLift 2401757
  have htrace : WordTrace (prefixWord ++ tailWord_2401757) baseStart_2401757 baseEnd_2401757 := by
    simpa [prefixWord, tailWord_2401757, baseEnd_2401757] using wordTrace_append hprefix tailTrace_2401757
  have hstable : (prefixWord ++ tailWord_2401757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401757).length < 2 ^ (prefixWord ++ tailWord_2401757).sum := by decide
  have hdescent : baseEnd_2401757 < baseStart_2401757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401793 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2401793 : Nat := 118140960795 + 2401793 * 2 ^ 59
def prefixEnd_2401793 : Nat := 4983230072969 + 3 ^ 40 * 2401793 * 2
def baseEnd_2401793 : Nat := 1233274241604226707541861

theorem tailTrace_2401793 : CollatzResearch.WordTrace tailWord_2401793 prefixEnd_2401793 1233274241604226707541861 := by
  unfold tailWord_2401793
  simp only [CollatzResearch.WordTrace]
  refine ⟨87600587387721629432330033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58400391591814419621553355 87600587387721629432330033)
  ·
    refine ⟨65700440540791222074247525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87600587387721629432330033 65700440540791222074247525)
    ·
      refine ⟨12318832601398354138921411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65700440540791222074247525 12318832601398354138921411)
      ·
        refine ⟨18478248902097531208382117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12318832601398354138921411 18478248902097531208382117)
        ·
          refine ⟨3464671669143287101571647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18478248902097531208382117 3464671669143287101571647)
          ·
            refine ⟨5197007503714930652357471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464671669143287101571647 5197007503714930652357471)
            ·
              refine ⟨7795511255572395978536207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197007503714930652357471 7795511255572395978536207)
              ·
                refine ⟨11693266883358593967804311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7795511255572395978536207 11693266883358593967804311)
                ·
                  refine ⟨17539900325037890951706467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11693266883358593967804311 17539900325037890951706467)
                  ·
                    refine ⟨26309850487556836427559701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17539900325037890951706467 26309850487556836427559701)
                    ·
                      refine ⟨1233274241604226707541861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26309850487556836427559701 1233274241604226707541861)
                      ·
                        rfl

theorem cell23_2401793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2401793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401793 prefixEnd_2401793 := by exact prefixLift 2401793
  have htrace : WordTrace (prefixWord ++ tailWord_2401793) baseStart_2401793 baseEnd_2401793 := by
    simpa [prefixWord, tailWord_2401793, baseEnd_2401793] using wordTrace_append hprefix tailTrace_2401793
  have hstable : (prefixWord ++ tailWord_2401793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401793).length < 2 ^ (prefixWord ++ tailWord_2401793).sum := by decide
  have hdescent : baseEnd_2401793 < baseStart_2401793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401847 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_2401847 : Nat := 118140960795 + 2401847 * 2 ^ 59
def prefixEnd_2401847 : Nat := 4983230072969 + 3 ^ 40 * 2401847 * 2
def baseEnd_2401847 : Nat := 1233301969559569496266613

theorem tailTrace_2401847 : CollatzResearch.WordTrace tailWord_2401847 prefixEnd_2401847 1233301969559569496266613 := by
  unfold tailWord_2401847
  simp only [CollatzResearch.WordTrace]
  refine ⟨87602556929525996654795795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58401704619683997769863863 87602556929525996654795795)
  ·
    refine ⟨131403835394288994982193693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87602556929525996654795795 131403835394288994982193693)
    ·
      refine ⟨49276438272858373118322635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131403835394288994982193693 49276438272858373118322635)
      ·
        refine ⟨73914657409287559677483953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49276438272858373118322635 73914657409287559677483953)
        ·
          refine ⟨55435993056965669758112965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73914657409287559677483953 55435993056965669758112965)
          ·
            refine ⟨10394248698181063079646181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55435993056965669758112965 10394248698181063079646181)
            ·
              refine ⟨1948921630908949327433659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10394248698181063079646181 1948921630908949327433659)
              ·
                refine ⟨2923382446363423991150489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948921630908949327433659 2923382446363423991150489)
                ·
                  refine ⟨2192536834772567993362867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923382446363423991150489 2192536834772567993362867)
                  ·
                    refine ⟨3288805252158851990044301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192536834772567993362867 3288805252158851990044301)
                    ·
                      refine ⟨1233301969559569496266613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288805252158851990044301 1233301969559569496266613)
                      ·
                        rfl

theorem cell23_2401847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_2401847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401847 prefixEnd_2401847 := by exact prefixLift 2401847
  have htrace : WordTrace (prefixWord ++ tailWord_2401847) baseStart_2401847 baseEnd_2401847 := by
    simpa [prefixWord, tailWord_2401847, baseEnd_2401847] using wordTrace_append hprefix tailTrace_2401847
  have hstable : (prefixWord ++ tailWord_2401847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401847).length < 2 ^ (prefixWord ++ tailWord_2401847).sum := by decide
  have hdescent : baseEnd_2401847 < baseStart_2401847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401874 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_2401874 : Nat := 118140960795 + 2401874 * 2 ^ 59
def prefixEnd_2401874 : Nat := 4983230072969 + 3 ^ 40 * 2401874 * 2
def baseEnd_2401874 : Nat := 1233315833537240890628989

theorem tailTrace_2401874 : CollatzResearch.WordTrace tailWord_2401874 prefixEnd_2401874 1233315833537240890628989 := by
  unfold tailWord_2401874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900885425107045066507169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58402361133618786844019117 21900885425107045066507169)
  ·
    refine ⟨16425664068830283799880377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21900885425107045066507169 16425664068830283799880377)
    ·
      refine ⟨12319248051622712849910283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16425664068830283799880377 12319248051622712849910283)
      ·
        refine ⟨18478872077434069274865425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12319248051622712849910283 18478872077434069274865425)
        ·
          refine ⟨13859154058075551956149069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18478872077434069274865425 13859154058075551956149069)
          ·
            refine ⟨5197182771778331983555901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13859154058075551956149069 5197182771778331983555901)
            ·
              refine ⟨1948943539416874493833463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5197182771778331983555901 1948943539416874493833463)
              ·
                refine ⟨2923415309125311740750195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948943539416874493833463 2923415309125311740750195)
                ·
                  refine ⟨4385122963687967611125293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923415309125311740750195 4385122963687967611125293)
                  ·
                    refine ⟨1644421111382987854171985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4385122963687967611125293 1644421111382987854171985)
                    ·
                      refine ⟨1233315833537240890628989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644421111382987854171985 1233315833537240890628989)
                      ·
                        rfl

theorem cell23_2401874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_2401874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401874 prefixEnd_2401874 := by exact prefixLift 2401874
  have htrace : WordTrace (prefixWord ++ tailWord_2401874) baseStart_2401874 baseEnd_2401874 := by
    simpa [prefixWord, tailWord_2401874, baseEnd_2401874] using wordTrace_append hprefix tailTrace_2401874
  have hstable : (prefixWord ++ tailWord_2401874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401874).length < 2 ^ (prefixWord ++ tailWord_2401874).sum := by decide
  have hdescent : baseEnd_2401874 < baseStart_2401874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401910 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2401910 : Nat := 118140960795 + 2401910 * 2 ^ 59
def prefixEnd_2401910 : Nat := 4983230072969 + 3 ^ 40 * 2401910 * 2
def baseEnd_2401910 : Nat := 137037146537866972197647

theorem tailTrace_2401910 : CollatzResearch.WordTrace tailWord_2401910 prefixEnd_2401910 137037146537866972197647 := by
  unfold tailWord_2401910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5475303420518609900896199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58403236485531838942892789 5475303420518609900896199)
  ·
    refine ⟨8212955130777914851344299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5475303420518609900896199 8212955130777914851344299)
    ·
      refine ⟨12319432696166872277016449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8212955130777914851344299 12319432696166872277016449)
      ·
        refine ⟨9239574522125154207762337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12319432696166872277016449 9239574522125154207762337)
        ·
          refine ⟨6929680891593865655821753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9239574522125154207762337 6929680891593865655821753)
          ·
            refine ⟨5197260668695399241866315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929680891593865655821753 5197260668695399241866315)
            ·
              refine ⟨7795891003043098862799473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197260668695399241866315 7795891003043098862799473)
              ·
                refine ⟨5846918252282324147099605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795891003043098862799473 5846918252282324147099605)
                ·
                  refine ⟨137037146537866972197647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5846918252282324147099605 137037146537866972197647)
                  ·
                    rfl

theorem cell23_2401910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2401910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401910 prefixEnd_2401910 := by exact prefixLift 2401910
  have htrace : WordTrace (prefixWord ++ tailWord_2401910) baseStart_2401910 baseEnd_2401910 := by
    simpa [prefixWord, tailWord_2401910, baseEnd_2401910] using wordTrace_append hprefix tailTrace_2401910
  have hstable : (prefixWord ++ tailWord_2401910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401910).length < 2 ^ (prefixWord ++ tailWord_2401910).sum := by decide
  have hdescent : baseEnd_2401910 < baseStart_2401910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401936 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_2401936 : Nat := 118140960795 + 2401936 * 2 ^ 59
def prefixEnd_2401936 : Nat := 4983230072969 + 3 ^ 40 * 2401936 * 2
def baseEnd_2401936 : Nat := 411115889779273216017901

theorem tailTrace_2401936 : CollatzResearch.WordTrace tailWord_2401936 prefixEnd_2401936 411115889779273216017901 := by
  unfold tailWord_2401936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43802901513101782427392831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58403868684135709903190441 43802901513101782427392831)
  ·
    refine ⟨65704352269652673641089247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43802901513101782427392831 65704352269652673641089247)
    ·
      refine ⟨98556528404479010461633871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65704352269652673641089247 98556528404479010461633871)
      ·
        refine ⟨147834792606718515692450807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98556528404479010461633871 147834792606718515692450807)
        ·
          refine ⟨221752188910077773538676211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147834792606718515692450807 221752188910077773538676211)
          ·
            refine ⟨332628283365116660308014317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221752188910077773538676211 332628283365116660308014317)
            ·
              refine ⟨124735606261918747615505369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332628283365116660308014317 124735606261918747615505369)
              ·
                refine ⟨93551704696439060711629027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124735606261918747615505369 93551704696439060711629027)
                ·
                  refine ⟨140327557044658591067443541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93551704696439060711629027 140327557044658591067443541)
                  ·
                    refine ⟨411115889779273216017901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 140327557044658591067443541 411115889779273216017901)
                    ·
                      rfl

theorem cell23_2401936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_2401936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401936 prefixEnd_2401936 := by exact prefixLift 2401936
  have htrace : WordTrace (prefixWord ++ tailWord_2401936) baseStart_2401936 baseEnd_2401936 := by
    simpa [prefixWord, tailWord_2401936, baseEnd_2401936] using wordTrace_append hprefix tailTrace_2401936
  have hstable : (prefixWord ++ tailWord_2401936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401936).length < 2 ^ (prefixWord ++ tailWord_2401936).sum := by decide
  have hdescent : baseEnd_2401936 < baseStart_2401936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401938 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_2401938 : Nat := 118140960795 + 2401938 * 2 ^ 59
def prefixEnd_2401938 : Nat := 4983230072969 + 3 ^ 40 * 2401938 * 2
def baseEnd_2401938 : Nat := 1233348696299128640228695

theorem tailTrace_2401938 : CollatzResearch.WordTrace tailWord_2401938 prefixEnd_2401938 1233348696299128640228695 := by
  unfold tailWord_2401938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901468993049079799089617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58403917314797546130905645 21901468993049079799089617)
  ·
    refine ⟨16426101744786809849317213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21901468993049079799089617 16426101744786809849317213)
    ·
      refine ⟨6159788154295053693493955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16426101744786809849317213 6159788154295053693493955)
      ·
        refine ⟨9239682231442580540240933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159788154295053693493955 9239682231442580540240933)
        ·
          refine ⟨1732440418395483851295175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9239682231442580540240933 1732440418395483851295175)
          ·
            refine ⟨2598660627593225776942763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732440418395483851295175 2598660627593225776942763)
            ·
              refine ⟨3897990941389838665414145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598660627593225776942763 3897990941389838665414145)
              ·
                refine ⟨2923493206042378999060609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3897990941389838665414145 2923493206042378999060609)
                ·
                  refine ⟨2192619904531784249295457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923493206042378999060609 2192619904531784249295457)
                  ·
                    refine ⟨1644464928398838186971593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192619904531784249295457 1644464928398838186971593)
                    ·
                      refine ⟨1233348696299128640228695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644464928398838186971593 1233348696299128640228695)
                      ·
                        rfl

theorem cell23_2401938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_2401938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401938 prefixEnd_2401938 := by exact prefixLift 2401938
  have htrace : WordTrace (prefixWord ++ tailWord_2401938) baseStart_2401938 baseEnd_2401938 := by
    simpa [prefixWord, tailWord_2401938, baseEnd_2401938] using wordTrace_append hprefix tailTrace_2401938
  have hstable : (prefixWord ++ tailWord_2401938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401938).length < 2 ^ (prefixWord ++ tailWord_2401938).sum := by decide
  have hdescent : baseEnd_2401938 < baseStart_2401938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401970 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_2401970 : Nat := 118140960795 + 2401970 * 2 ^ 59
def prefixEnd_2401970 : Nat := 4983230072969 + 3 ^ 40 * 2401970 * 2
def baseEnd_2401970 : Nat := 411121709226690838342849

theorem tailTrace_2401970 : CollatzResearch.WordTrace tailWord_2401970 prefixEnd_2401970 411121709226690838342849 := by
  unfold tailWord_2401970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901760777020097165380841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58404695405386925774348909 21901760777020097165380841)
  ·
    refine ⟨16426320582765072874035631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21901760777020097165380841 16426320582765072874035631)
    ·
      refine ⟨24639480874147609311053447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16426320582765072874035631 24639480874147609311053447)
      ·
        refine ⟨36959221311221413966580171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24639480874147609311053447 36959221311221413966580171)
        ·
          refine ⟨55438831966832120949870257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36959221311221413966580171 55438831966832120949870257)
          ·
            refine ⟨41579123975124090712402693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55438831966832120949870257 41579123975124090712402693)
            ·
              refine ⟨7796085745335767008575505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41579123975124090712402693 7796085745335767008575505)
              ·
                refine ⟨5847064309001825256431629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7796085745335767008575505 5847064309001825256431629)
                ·
                  refine ⟨2192649115875684471161861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5847064309001825256431629 2192649115875684471161861)
                  ·
                    refine ⟨411121709226690838342849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192649115875684471161861 411121709226690838342849)
                    ·
                      rfl

theorem cell23_2401970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_2401970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401970 prefixEnd_2401970 := by exact prefixLift 2401970
  have htrace : WordTrace (prefixWord ++ tailWord_2401970) baseStart_2401970 baseEnd_2401970 := by
    simpa [prefixWord, tailWord_2401970, baseEnd_2401970] using wordTrace_append hprefix tailTrace_2401970
  have hstable : (prefixWord ++ tailWord_2401970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401970).length < 2 ^ (prefixWord ++ tailWord_2401970).sum := by decide
  have hdescent : baseEnd_2401970 < baseStart_2401970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2401980 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2401980 : Nat := 118140960795 + 2401980 * 2 ^ 59
def prefixEnd_2401980 : Nat := 4983230072969 + 3 ^ 40 * 2401980 * 2
def baseEnd_2401980 : Nat := 1233370262486617475903501

theorem tailTrace_2401980 : CollatzResearch.WordTrace tailWord_2401980 prefixEnd_2401980 1233370262486617475903501 := by
  unfold tailWord_2401980
  simp only [CollatzResearch.WordTrace]
  refine ⟨43803703919022080184693697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58404938558696106912924929 43803703919022080184693697)
  ·
    refine ⟨32852777939266560138520273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43803703919022080184693697 32852777939266560138520273)
    ·
      refine ⟨24639583454449920103890205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32852777939266560138520273 24639583454449920103890205)
      ·
        refine ⟨9239843795418720038958827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24639583454449920103890205 9239843795418720038958827)
        ·
          refine ⟨13859765693128080058438241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239843795418720038958827 13859765693128080058438241)
          ·
            refine ⟨10394824269846060043828681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13859765693128080058438241 10394824269846060043828681)
            ·
              refine ⟨7796118202384545032871511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10394824269846060043828681 7796118202384545032871511)
              ·
                refine ⟨11694177303576817549307267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796118202384545032871511 11694177303576817549307267)
                ·
                  refine ⟨17541265955365226323960901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11694177303576817549307267 17541265955365226323960901)
                  ·
                    refine ⟨3288987366630979935742669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17541265955365226323960901 3288987366630979935742669)
                    ·
                      refine ⟨1233370262486617475903501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3288987366630979935742669 1233370262486617475903501)
                      ·
                        rfl

theorem cell23_2401980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2401980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2401980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2401980 prefixEnd_2401980 := by exact prefixLift 2401980
  have htrace : WordTrace (prefixWord ++ tailWord_2401980) baseStart_2401980 baseEnd_2401980 := by
    simpa [prefixWord, tailWord_2401980, baseEnd_2401980] using wordTrace_append hprefix tailTrace_2401980
  have hstable : (prefixWord ++ tailWord_2401980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2401980).length < 2 ^ (prefixWord ++ tailWord_2401980).sum := by decide
  have hdescent : baseEnd_2401980 < baseStart_2401980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2401980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402004 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_2402004 : Nat := 118140960795 + 2402004 * 2 ^ 59
def prefixEnd_2402004 : Nat := 4983230072969 + 3 ^ 40 * 2402004 * 2
def baseEnd_2402004 : Nat := 411127528674108460667797

theorem tailTrace_2402004 : CollatzResearch.WordTrace tailWord_2402004 prefixEnd_2402004 411127528674108460667797 := by
  unfold tailWord_2402004
  simp only [CollatzResearch.WordTrace]
  refine ⟨43804141594978606234130533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58405522126638141645507377 43804141594978606234130533)
  ·
    refine ⟨8213276549058488668899475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43804141594978606234130533 8213276549058488668899475)
    ·
      refine ⟨12319914823587733003349213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8213276549058488668899475 12319914823587733003349213)
      ·
        refine ⟨4619968058845399876255955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12319914823587733003349213 4619968058845399876255955)
        ·
          refine ⟨6929952088268099814383933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619968058845399876255955 6929952088268099814383933)
          ·
            refine ⟨2598732033100537430393975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6929952088268099814383933 2598732033100537430393975)
            ·
              refine ⟨3898098049650806145590963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598732033100537430393975 3898098049650806145590963)
              ·
                refine ⟨5847147074476209218386445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898098049650806145590963 5847147074476209218386445)
                ·
                  refine ⟨2192680152928578456894917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5847147074476209218386445 2192680152928578456894917)
                  ·
                    refine ⟨411127528674108460667797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192680152928578456894917 411127528674108460667797)
                    ·
                      rfl

theorem cell23_2402004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_2402004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402004 prefixEnd_2402004 := by exact prefixLift 2402004
  have htrace : WordTrace (prefixWord ++ tailWord_2402004) baseStart_2402004 baseEnd_2402004 := by
    simpa [prefixWord, tailWord_2402004, baseEnd_2402004] using wordTrace_append hprefix tailTrace_2402004
  have hstable : (prefixWord ++ tailWord_2402004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402004).length < 2 ^ (prefixWord ++ tailWord_2402004).sum := by decide
  have hdescent : baseEnd_2402004 < baseStart_2402004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402030 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2402030 : Nat := 118140960795 + 2402030 * 2 ^ 59
def prefixEnd_2402030 : Nat := 4983230072969 + 3 ^ 40 * 2402030 * 2
def baseEnd_2402030 : Nat := 411131978839780760092757

theorem tailTrace_2402030 : CollatzResearch.WordTrace tailWord_2402030 prefixEnd_2402030 411131978839780760092757 := by
  unfold tailWord_2402030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10951153935982877363588443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58406154325242012605805029 10951153935982877363588443)
  ·
    refine ⟨16426730903974316045382665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10951153935982877363588443 16426730903974316045382665)
    ·
      refine ⟨12320048177980737034036999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16426730903974316045382665 12320048177980737034036999)
      ·
        refine ⟨18480072266971105551055499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12320048177980737034036999 18480072266971105551055499)
        ·
          refine ⟨27720108400456658326583249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18480072266971105551055499 27720108400456658326583249)
          ·
            refine ⟨20790081300342493744937437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27720108400456658326583249 20790081300342493744937437)
            ·
              refine ⟨7796280487628435154351539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20790081300342493744937437 7796280487628435154351539)
              ·
                refine ⟨11694420731442652731527309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796280487628435154351539 11694420731442652731527309)
                ·
                  refine ⟨4385407774290994774322741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11694420731442652731527309 4385407774290994774322741)
                  ·
                    refine ⟨411131978839780760092757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4385407774290994774322741 411131978839780760092757)
                    ·
                      rfl

theorem cell23_2402030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2402030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402030 prefixEnd_2402030 := by exact prefixLift 2402030
  have htrace : WordTrace (prefixWord ++ tailWord_2402030) baseStart_2402030 baseEnd_2402030 := by
    simpa [prefixWord, tailWord_2402030, baseEnd_2402030] using wordTrace_append hprefix tailTrace_2402030
  have hstable : (prefixWord ++ tailWord_2402030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402030).length < 2 ^ (prefixWord ++ tailWord_2402030).sum := by decide
  have hdescent : baseEnd_2402030 < baseStart_2402030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402044 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_2402044 : Nat := 118140960795 + 2402044 * 2 ^ 59
def prefixEnd_2402044 : Nat := 4983230072969 + 3 ^ 40 * 2402044 * 2
def baseEnd_2402044 : Nat := 1233403125248505225503207

theorem tailTrace_2402044 : CollatzResearch.WordTrace tailWord_2402044 prefixEnd_2402044 1233403125248505225503207 := by
  unfold tailWord_2402044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43804871054906149649858593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58406494739874866199811457 43804871054906149649858593)
  ·
    refine ⟨32853653291179612237393945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43804871054906149649858593 32853653291179612237393945)
    ·
      refine ⟨24640239968384709178045459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32853653291179612237393945 24640239968384709178045459)
      ·
        refine ⟨36960359952577063767068189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24640239968384709178045459 36960359952577063767068189)
        ·
          refine ⟨13860134982216398912650571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36960359952577063767068189 13860134982216398912650571)
          ·
            refine ⟨20790202473324598368975857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13860134982216398912650571 20790202473324598368975857)
            ·
              refine ⟨15592651854993448776731893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20790202473324598368975857 15592651854993448776731893)
              ·
                refine ⟨1461811111405635822818615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15592651854993448776731893 1461811111405635822818615)
                ·
                  refine ⟨2192716667108453734227923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461811111405635822818615 2192716667108453734227923)
                  ·
                    refine ⟨3289075000662680601341885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192716667108453734227923 3289075000662680601341885)
                    ·
                      refine ⟨1233403125248505225503207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289075000662680601341885 1233403125248505225503207)
                      ·
                        rfl

theorem cell23_2402044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_2402044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402044 prefixEnd_2402044 := by exact prefixLift 2402044
  have htrace : WordTrace (prefixWord ++ tailWord_2402044) baseStart_2402044 baseEnd_2402044 := by
    simpa [prefixWord, tailWord_2402044, baseEnd_2402044] using wordTrace_append hprefix tailTrace_2402044
  have hstable : (prefixWord ++ tailWord_2402044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402044).length < 2 ^ (prefixWord ++ tailWord_2402044).sum := by decide
  have hdescent : baseEnd_2402044 < baseStart_2402044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402060 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_2402060 : Nat := 118140960795 + 2402060 * 2 ^ 59
def prefixEnd_2402060 : Nat := 4983230072969 + 3 ^ 40 * 2402060 * 2
def baseEnd_2402060 : Nat := 411137113646325720967711

theorem tailTrace_2402060 : CollatzResearch.WordTrace tailWord_2402060 prefixEnd_2402060 411137113646325720967711 := by
  unfold tailWord_2402060
  simp only [CollatzResearch.WordTrace]
  refine ⟨43805162838877167016149817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58406883785169556021533089 43805162838877167016149817)
  ·
    refine ⟨32853872129157875262112363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43805162838877167016149817 32853872129157875262112363)
    ·
      refine ⟨49280808193736812893168545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32853872129157875262112363 49280808193736812893168545)
      ·
        refine ⟨36960606145302609669876409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49280808193736812893168545 36960606145302609669876409)
        ·
          refine ⟨27720454608976957252407307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36960606145302609669876409 27720454608976957252407307)
          ·
            refine ⟨41580681913465435878610961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27720454608976957252407307 41580681913465435878610961)
            ·
              refine ⟨31185511435099076908958221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41580681913465435878610961 31185511435099076908958221)
              ·
                refine ⟨11694566788162153840859333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31185511435099076908958221 11694566788162153840859333)
                ·
                  refine ⟨2192731272780403845161125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11694566788162153840859333 2192731272780403845161125)
                  ·
                    refine ⟨411137113646325720967711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192731272780403845161125 411137113646325720967711)
                    ·
                      rfl

theorem cell23_2402060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_2402060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402060 prefixEnd_2402060 := by exact prefixLift 2402060
  have htrace : WordTrace (prefixWord ++ tailWord_2402060) baseStart_2402060 baseEnd_2402060 := by
    simpa [prefixWord, tailWord_2402060, baseEnd_2402060] using wordTrace_append hprefix tailTrace_2402060
  have hstable : (prefixWord ++ tailWord_2402060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402060).length < 2 ^ (prefixWord ++ tailWord_2402060).sum := by decide
  have hdescent : baseEnd_2402060 < baseStart_2402060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402063 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_2402063 : Nat := 118140960795 + 2402063 * 2 ^ 59
def prefixEnd_2402063 : Nat := 4983230072969 + 3 ^ 40 * 2402063 * 2
def baseEnd_2402063 : Nat := 1233412881380940651165619

theorem tailTrace_2402063 : CollatzResearch.WordTrace tailWord_2402063 prefixEnd_2402063 1233412881380940651165619 := by
  unfold tailWord_2402063
  simp only [CollatzResearch.WordTrace]
  refine ⟨87610435096743465544658843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58406956731162310363105895 87610435096743465544658843)
  ·
    refine ⟨131415652645115198316988265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87610435096743465544658843 131415652645115198316988265)
    ·
      refine ⟨98561739483836398737741199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131415652645115198316988265 98561739483836398737741199)
      ·
        refine ⟨147842609225754598106611799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98561739483836398737741199 147842609225754598106611799)
        ·
          refine ⟨221763913838631897159917699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147842609225754598106611799 221763913838631897159917699)
          ·
            refine ⟨332645870757947845739876549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221763913838631897159917699 332645870757947845739876549)
            ·
              refine ⟨62371100767115221076226853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332645870757947845739876549 62371100767115221076226853)
              ·
                refine ⟨11694581393834103951792535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62371100767115221076226853 11694581393834103951792535)
                ·
                  refine ⟨17541872090751155927688803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11694581393834103951792535 17541872090751155927688803)
                  ·
                    refine ⟨26312808136126733891533205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17541872090751155927688803 26312808136126733891533205)
                    ·
                      refine ⟨1233412881380940651165619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26312808136126733891533205 1233412881380940651165619)
                      ·
                        rfl

theorem cell23_2402063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_2402063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402063 prefixEnd_2402063 := by exact prefixLift 2402063
  have htrace : WordTrace (prefixWord ++ tailWord_2402063) baseStart_2402063 baseEnd_2402063 := by
    simpa [prefixWord, tailWord_2402063, baseEnd_2402063] using wordTrace_append hprefix tailTrace_2402063
  have hstable : (prefixWord ++ tailWord_2402063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402063).length < 2 ^ (prefixWord ++ tailWord_2402063).sum := by decide
  have hdescent : baseEnd_2402063 < baseStart_2402063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402078 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2402078 : Nat := 118140960795 + 2402078 * 2 ^ 59
def prefixEnd_2402078 : Nat := 4983230072969 + 3 ^ 40 * 2402078 * 2
def baseEnd_2402078 : Nat := 1233420583590758092478051

theorem tailTrace_2402078 : CollatzResearch.WordTrace tailWord_2402078 prefixEnd_2402078 1233420583590758092478051 := by
  unfold tailWord_2402078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10951372773961140388306861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58407321461126082070969925 10951372773961140388306861)
  ·
    refine ⟨4106764790235427645615073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10951372773961140388306861 4106764790235427645615073)
    ·
      refine ⟨3080073592676570734211305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4106764790235427645615073 3080073592676570734211305)
      ·
        refine ⟨2310055194507428050658479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3080073592676570734211305 2310055194507428050658479)
        ·
          refine ⟨3465082791761142075987719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310055194507428050658479 3465082791761142075987719)
          ·
            refine ⟨5197624187641713113981579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465082791761142075987719 5197624187641713113981579)
            ·
              refine ⟨7796436281462569670972369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197624187641713113981579 7796436281462569670972369)
              ·
                refine ⟨5847327211096927253229277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7796436281462569670972369 5847327211096927253229277)
                ·
                  refine ⟨2192747704161347719960979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5847327211096927253229277 2192747704161347719960979)
                  ·
                    refine ⟨3289121556242021579941469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192747704161347719960979 3289121556242021579941469)
                    ·
                      refine ⟨1233420583590758092478051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289121556242021579941469 1233420583590758092478051)
                      ·
                        rfl

theorem cell23_2402078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2402078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402078 prefixEnd_2402078 := by exact prefixLift 2402078
  have htrace : WordTrace (prefixWord ++ tailWord_2402078) baseStart_2402078 baseEnd_2402078 := by
    simpa [prefixWord, tailWord_2402078, baseEnd_2402078] using wordTrace_append hprefix tailTrace_2402078
  have hstable : (prefixWord ++ tailWord_2402078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402078).length < 2 ^ (prefixWord ++ tailWord_2402078).sum := by decide
  have hdescent : baseEnd_2402078 < baseStart_2402078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402084 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_2402084 : Nat := 118140960795 + 2402084 * 2 ^ 59
def prefixEnd_2402084 : Nat := 4983230072969 + 3 ^ 40 * 2402084 * 2
def baseEnd_2402084 : Nat := 1233423664474685069003023

theorem tailTrace_2402084 : CollatzResearch.WordTrace tailWord_2402084 prefixEnd_2402084 1233423664474685069003023 := by
  unfold tailWord_2402084
  simp only [CollatzResearch.WordTrace]
  refine ⟨43805600514833693065586653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58407467353111590754115537 43805600514833693065586653)
  ·
    refine ⟨16427100193062634899594995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43805600514833693065586653 16427100193062634899594995)
    ·
      refine ⟨24640650289593952349392493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16427100193062634899594995 24640650289593952349392493)
      ·
        refine ⟨9240243858597732131022185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24640650289593952349392493 9240243858597732131022185)
        ·
          refine ⟨6930182893948299098266639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9240243858597732131022185 6930182893948299098266639)
          ·
            refine ⟨10395274340922448647399959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930182893948299098266639 10395274340922448647399959)
            ·
              refine ⟨15592911511383672971099939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10395274340922448647399959 15592911511383672971099939)
              ·
                refine ⟨23389367267075509456649909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15592911511383672971099939 23389367267075509456649909)
                ·
                  refine ⟨2192753181288329011560929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23389367267075509456649909 2192753181288329011560929)
                  ·
                    refine ⟨1644564885966246758670697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192753181288329011560929 1644564885966246758670697)
                    ·
                      refine ⟨1233423664474685069003023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644564885966246758670697 1233423664474685069003023)
                      ·
                        rfl

theorem cell23_2402084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_2402084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402084 prefixEnd_2402084 := by exact prefixLift 2402084
  have htrace : WordTrace (prefixWord ++ tailWord_2402084) baseStart_2402084 baseEnd_2402084 := by
    simpa [prefixWord, tailWord_2402084, baseEnd_2402084] using wordTrace_append hprefix tailTrace_2402084
  have hstable : (prefixWord ++ tailWord_2402084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402084).length < 2 ^ (prefixWord ++ tailWord_2402084).sum := by decide
  have hdescent : baseEnd_2402084 < baseStart_2402084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402101 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_2402101 : Nat := 118140960795 + 2402101 * 2 ^ 59
def prefixEnd_2402101 : Nat := 4983230072969 + 3 ^ 40 * 2402101 * 2
def baseEnd_2402101 : Nat := 1233432393645811502490445

theorem tailTrace_2402101 : CollatzResearch.WordTrace tailWord_2402101 prefixEnd_2402101 1233432393645811502490445 := by
  unfold tailWord_2402101
  simp only [CollatzResearch.WordTrace]
  refine ⟨87611821070605798034542157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58407880713737198689694771 87611821070605798034542157)
  ·
    refine ⟨32854432901477174262953309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87611821070605798034542157 32854432901477174262953309)
    ·
      refine ⟨12320412338053940348607491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32854432901477174262953309 12320412338053940348607491)
      ·
        refine ⟨18480618507080910522911237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12320412338053940348607491 18480618507080910522911237)
        ·
          refine ⟨3465115970077670723045857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18480618507080910522911237 3465115970077670723045857)
          ·
            refine ⟨2598836977558253042284393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465115970077670723045857 2598836977558253042284393)
            ·
              refine ⟨1949127733168689781713295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2598836977558253042284393 1949127733168689781713295)
              ·
                refine ⟨2923691599753034672569943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949127733168689781713295 2923691599753034672569943)
                ·
                  refine ⟨4385537399629552008854915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923691599753034672569943 4385537399629552008854915)
                  ·
                    refine ⟨6578306099444328013282373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4385537399629552008854915 6578306099444328013282373)
                    ·
                      refine ⟨1233432393645811502490445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6578306099444328013282373 1233432393645811502490445)
                      ·
                        rfl

theorem cell23_2402101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_2402101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402101 prefixEnd_2402101 := by exact prefixLift 2402101
  have htrace : WordTrace (prefixWord ++ tailWord_2402101) baseStart_2402101 baseEnd_2402101 := by
    simpa [prefixWord, tailWord_2402101, baseEnd_2402101] using wordTrace_append hprefix tailTrace_2402101
  have hstable : (prefixWord ++ tailWord_2402101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402101).length < 2 ^ (prefixWord ++ tailWord_2402101).sum := by decide
  have hdescent : baseEnd_2402101 < baseStart_2402101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402103 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 9]
def baseStart_2402103 : Nat := 118140960795 + 2402103 * 2 ^ 59
def prefixEnd_2402103 : Nat := 4983230072969 + 3 ^ 40 * 2402103 * 2
def baseEnd_2402103 : Nat := 411144473535706831555145

theorem tailTrace_2402103 : CollatzResearch.WordTrace tailWord_2402103 prefixEnd_2402103 411144473535706831555145 := by
  unfold tailWord_2402103
  simp only [CollatzResearch.WordTrace]
  refine ⟨87611894016598552376114963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58407929344399034917409975 87611894016598552376114963)
  ·
    refine ⟨131417841024897828564172445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87611894016598552376114963 131417841024897828564172445)
    ·
      refine ⟨49281690384336685711564667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131417841024897828564172445 49281690384336685711564667)
      ·
        refine ⟨73922535576505028567347001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49281690384336685711564667 73922535576505028567347001)
        ·
          refine ⟨55441901682378771425510251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73922535576505028567347001 55441901682378771425510251)
          ·
            refine ⟨83162852523568157138265377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55441901682378771425510251 83162852523568157138265377)
            ·
              refine ⟨62372139392676117853699033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83162852523568157138265377 62372139392676117853699033)
              ·
                refine ⟨46779104544507088390274275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62372139392676117853699033 46779104544507088390274275)
                ·
                  refine ⟨70168656816760632585411413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46779104544507088390274275 70168656816760632585411413)
                  ·
                    refine ⟨411144473535706831555145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 70168656816760632585411413 411144473535706831555145)
                    ·
                      rfl

theorem cell23_2402103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_2402103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402103 prefixEnd_2402103 := by exact prefixLift 2402103
  have htrace : WordTrace (prefixWord ++ tailWord_2402103) baseStart_2402103 baseEnd_2402103 := by
    simpa [prefixWord, tailWord_2402103, baseEnd_2402103] using wordTrace_append hprefix tailTrace_2402103
  have hstable : (prefixWord ++ tailWord_2402103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402103).length < 2 ^ (prefixWord ++ tailWord_2402103).sum := by decide
  have hdescent : baseEnd_2402103 < baseStart_2402103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402104 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_2402104 : Nat := 118140960795 + 2402104 * 2 ^ 59
def prefixEnd_2402104 : Nat := 4983230072969 + 3 ^ 40 * 2402104 * 2
def baseEnd_2402104 : Nat := 1233433934087774990752931

theorem tailTrace_2402104 : CollatzResearch.WordTrace tailWord_2402104 prefixEnd_2402104 1233433934087774990752931 := by
  unfold tailWord_2402104
  simp only [CollatzResearch.WordTrace]
  refine ⟨43805965244797464773450683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58407953659729953031267577 43805965244797464773450683)
  ·
    refine ⟨65708947867196197160176025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43805965244797464773450683 65708947867196197160176025)
    ·
      refine ⟨49281710900397147870132019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65708947867196197160176025 49281710900397147870132019)
      ·
        refine ⟨73922566350595721805198029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49281710900397147870132019 73922566350595721805198029)
        ·
          refine ⟨27720962381473395676949261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73922566350595721805198029 27720962381473395676949261)
          ·
            refine ⟨10395360893052523378855973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27720962381473395676949261 10395360893052523378855973)
            ·
              refine ⟨1949130167447348133535495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10395360893052523378855973 1949130167447348133535495)
              ·
                refine ⟨2923695251171022200303243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949130167447348133535495 2923695251171022200303243)
                ·
                  refine ⟨4385542876756533300454865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923695251171022200303243 4385542876756533300454865)
                  ·
                    refine ⟨3289157157567399975341149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4385542876756533300454865 3289157157567399975341149)
                    ·
                      refine ⟨1233433934087774990752931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289157157567399975341149 1233433934087774990752931)
                      ·
                        rfl

theorem cell23_2402104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_2402104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402104 prefixEnd_2402104 := by exact prefixLift 2402104
  have htrace : WordTrace (prefixWord ++ tailWord_2402104) baseStart_2402104 baseEnd_2402104 := by
    simpa [prefixWord, tailWord_2402104, baseEnd_2402104] using wordTrace_append hprefix tailTrace_2402104
  have hstable : (prefixWord ++ tailWord_2402104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402104).length < 2 ^ (prefixWord ++ tailWord_2402104).sum := by decide
  have hdescent : baseEnd_2402104 < baseStart_2402104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402111 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 2, 4]
def baseStart_2402111 : Nat := 118140960795 + 2402111 * 2 ^ 59
def prefixEnd_2402111 : Nat := 4983230072969 + 3 ^ 40 * 2402111 * 2
def baseEnd_2402111 : Nat := 411145842817452154455133

theorem tailTrace_2402111 : CollatzResearch.WordTrace tailWord_2402111 prefixEnd_2402111 411145842817452154455133 := by
  unfold tailWord_2402111
  simp only [CollatzResearch.WordTrace]
  refine ⟨87612185800569569742406187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58408123867046379828270791 87612185800569569742406187)
  ·
    refine ⟨131418278700854354613609281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87612185800569569742406187 131418278700854354613609281)
    ·
      refine ⟨98563709025640765960206961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131418278700854354613609281 98563709025640765960206961)
      ·
        refine ⟨73922781769230574470155221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98563709025640765960206961 73922781769230574470155221)
        ·
          refine ⟨1732565197716341589144263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 73922781769230574470155221 1732565197716341589144263)
          ·
            refine ⟨2598847796574512383716395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732565197716341589144263 2598847796574512383716395)
            ·
              refine ⟨3898271694861768575574593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598847796574512383716395 3898271694861768575574593)
              ·
                refine ⟨2923703771146326431680945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898271694861768575574593 2923703771146326431680945)
                ·
                  refine ⟨2192777828359744823760709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923703771146326431680945 2192777828359744823760709)
                  ·
                    refine ⟨411145842817452154455133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192777828359744823760709 411145842817452154455133)
                    ·
                      rfl

theorem cell23_2402111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_2402111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402111 prefixEnd_2402111 := by exact prefixLift 2402111
  have htrace : WordTrace (prefixWord ++ tailWord_2402111) baseStart_2402111 baseEnd_2402111 := by
    simpa [prefixWord, tailWord_2402111, baseEnd_2402111] using wordTrace_append hprefix tailTrace_2402111
  have hstable : (prefixWord ++ tailWord_2402111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402111).length < 2 ^ (prefixWord ++ tailWord_2402111).sum := by decide
  have hdescent : baseEnd_2402111 < baseStart_2402111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402117 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_2402117 : Nat := 118140960795 + 2402117 * 2 ^ 59
def prefixEnd_2402117 : Nat := 4983230072969 + 3 ^ 40 * 2402117 * 2
def baseEnd_2402117 : Nat := 1233440609336283439890371

theorem tailTrace_2402117 : CollatzResearch.WordTrace tailWord_2402117 prefixEnd_2402117 1233440609336283439890371 := by
  unfold tailWord_2402117
  simp only [CollatzResearch.WordTrace]
  refine ⟨87612404638547832767124605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58408269759031888511416403 87612404638547832767124605)
  ·
    refine ⟨32854651739455437287671727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87612404638547832767124605 32854651739455437287671727)
    ·
      refine ⟨49281977609183155931507591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32854651739455437287671727 49281977609183155931507591)
      ·
        refine ⟨73922966413774733897261387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49281977609183155931507591 73922966413774733897261387)
        ·
          refine ⟨110884449620662100845892081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73922966413774733897261387 110884449620662100845892081)
          ·
            refine ⟨83163337215496575634419061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110884449620662100845892081 83163337215496575634419061)
            ·
              refine ⟨7796562863952803965726787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83163337215496575634419061 7796562863952803965726787)
              ·
                refine ⟨11694844295929205948590181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796562863952803965726787 11694844295929205948590181)
                ·
                  refine ⟨2192783305486726115360659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11694844295929205948590181 2192783305486726115360659)
                  ·
                    refine ⟨3289174958230089173040989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192783305486726115360659 3289174958230089173040989)
                    ·
                      refine ⟨1233440609336283439890371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289174958230089173040989 1233440609336283439890371)
                      ·
                        rfl

theorem cell23_2402117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_2402117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402117 prefixEnd_2402117 := by exact prefixLift 2402117
  have htrace : WordTrace (prefixWord ++ tailWord_2402117) baseStart_2402117 baseEnd_2402117 := by
    simpa [prefixWord, tailWord_2402117, baseEnd_2402117] using wordTrace_append hprefix tailTrace_2402117
  have hstable : (prefixWord ++ tailWord_2402117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402117).length < 2 ^ (prefixWord ++ tailWord_2402117).sum := by decide
  have hdescent : baseEnd_2402117 < baseStart_2402117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402118 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2402118 : Nat := 118140960795 + 2402118 * 2 ^ 59
def prefixEnd_2402118 : Nat := 4983230072969 + 3 ^ 40 * 2402118 * 2
def baseEnd_2402118 : Nat := 1233441122816937935977867

theorem tailTrace_2402118 : CollatzResearch.WordTrace tailWord_2402118 prefixEnd_2402118 1233441122816937935977867 := by
  unfold tailWord_2402118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737888784735756560559719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58408294074362806625274005 2737888784735756560559719)
  ·
    refine ⟨4106833177103634840839579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2737888784735756560559719 4106833177103634840839579)
    ·
      refine ⟨6160249765655452261259369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4106833177103634840839579 6160249765655452261259369)
      ·
        refine ⟨4620187324241589195944527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160249765655452261259369 4620187324241589195944527)
        ·
          refine ⟨6930280986362383793916791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620187324241589195944527 6930280986362383793916791)
          ·
            refine ⟨10395421479543575690875187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930280986362383793916791 10395421479543575690875187)
            ·
              refine ⟨15593132219315363536312781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10395421479543575690875187 15593132219315363536312781)
              ·
                refine ⟨5847424582243261326117293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15593132219315363536312781 5847424582243261326117293)
                ·
                  refine ⟨2192784218341222997293985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5847424582243261326117293 2192784218341222997293985)
                  ·
                    refine ⟨1644588163755917247970489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192784218341222997293985 1644588163755917247970489)
                    ·
                      refine ⟨1233441122816937935977867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644588163755917247970489 1233441122816937935977867)
                      ·
                        rfl

theorem cell23_2402118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2402118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402118 prefixEnd_2402118 := by exact prefixLift 2402118
  have htrace : WordTrace (prefixWord ++ tailWord_2402118) baseStart_2402118 baseEnd_2402118 := by
    simpa [prefixWord, tailWord_2402118, baseEnd_2402118] using wordTrace_append hprefix tailTrace_2402118
  have hstable : (prefixWord ++ tailWord_2402118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402118).length < 2 ^ (prefixWord ++ tailWord_2402118).sum := by decide
  have hdescent : baseEnd_2402118 < baseStart_2402118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402144 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2]
def baseStart_2402144 : Nat := 118140960795 + 2402144 * 2 ^ 59
def prefixEnd_2402144 : Nat := 4983230072969 + 3 ^ 40 * 2402144 * 2
def baseEnd_2402144 : Nat := 1233454473313954834252747

theorem tailTrace_2402144 : CollatzResearch.WordTrace tailWord_2402144 prefixEnd_2402144 1233454473313954834252747 := by
  unfold tailWord_2402144
  simp only [CollatzResearch.WordTrace]
  refine ⟨43806694704725008189178743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58408926272966677585571657 43806694704725008189178743)
  ·
    refine ⟨65710042057087512283768115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43806694704725008189178743 65710042057087512283768115)
    ·
      refine ⟨98565063085631268425652173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65710042057087512283768115 98565063085631268425652173)
      ·
        refine ⟨36961898657111725659619565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98565063085631268425652173 36961898657111725659619565)
        ·
          refine ⟨13860711996416897122357337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36961898657111725659619565 13860711996416897122357337)
          ·
            refine ⟨10395533997312672841768003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13860711996416897122357337 10395533997312672841768003)
            ·
              refine ⟨15593300995969009262652005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10395533997312672841768003 15593300995969009262652005)
              ·
                refine ⟨2923743936744189236747251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15593300995969009262652005 2923743936744189236747251)
                ·
                  refine ⟨4385615905116283855120877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923743936744189236747251 4385615905116283855120877)
                  ·
                    refine ⟨1644605964418606445670329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4385615905116283855120877 1644605964418606445670329)
                    ·
                      refine ⟨1233454473313954834252747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644605964418606445670329 1233454473313954834252747)
                      ·
                        rfl

theorem cell23_2402144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_2402144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402144 prefixEnd_2402144 := by exact prefixLift 2402144
  have htrace : WordTrace (prefixWord ++ tailWord_2402144) baseStart_2402144 baseEnd_2402144 := by
    simpa [prefixWord, tailWord_2402144, baseEnd_2402144] using wordTrace_append hprefix tailTrace_2402144
  have hstable : (prefixWord ++ tailWord_2402144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402144).length < 2 ^ (prefixWord ++ tailWord_2402144).sum := by decide
  have hdescent : baseEnd_2402144 < baseStart_2402144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402160 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_2402160 : Nat := 118140960795 + 2402160 * 2 ^ 59
def prefixEnd_2402160 : Nat := 4983230072969 + 3 ^ 40 * 2402160 * 2
def baseEnd_2402160 : Nat := 1233462689004426771652673

theorem tailTrace_2402160 : CollatzResearch.WordTrace tailWord_2402160 prefixEnd_2402160 1233462689004426771652673 := by
  unfold tailWord_2402160
  simp only [CollatzResearch.WordTrace]
  refine ⟨43806986488696025555469967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58409315318261367407293289 43806986488696025555469967)
  ·
    refine ⟨65710479733044038333204951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43806986488696025555469967 65710479733044038333204951)
    ·
      refine ⟨98565719599566057499807427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65710479733044038333204951 98565719599566057499807427)
      ·
        refine ⟨147848579399349086249711141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98565719599566057499807427 147848579399349086249711141)
        ·
          refine ⟨27721608637377953671820839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147848579399349086249711141 27721608637377953671820839)
          ·
            refine ⟨41582412956066930507731259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27721608637377953671820839 41582412956066930507731259)
            ·
              refine ⟨62373619434100395761596889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41582412956066930507731259 62373619434100395761596889)
              ·
                refine ⟨46780214575575296821197667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62373619434100395761596889 46780214575575296821197667)
                ·
                  refine ⟨70170321863362945231796501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46780214575575296821197667 70170321863362945231796501)
                  ·
                    refine ⟨3289233837345138057740461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70170321863362945231796501 3289233837345138057740461)
                    ·
                      refine ⟨1233462689004426771652673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289233837345138057740461 1233462689004426771652673)
                      ·
                        rfl

theorem cell23_2402160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_2402160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402160 prefixEnd_2402160 := by exact prefixLift 2402160
  have htrace : WordTrace (prefixWord ++ tailWord_2402160) baseStart_2402160 baseEnd_2402160 := by
    simpa [prefixWord, tailWord_2402160, baseEnd_2402160] using wordTrace_append hprefix tailTrace_2402160
  have hstable : (prefixWord ++ tailWord_2402160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402160).length < 2 ^ (prefixWord ++ tailWord_2402160).sum := by decide
  have hdescent : baseEnd_2402160 < baseStart_2402160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402170 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_2402170 : Nat := 118140960795 + 2402170 * 2 ^ 59
def prefixEnd_2402170 : Nat := 4983230072969 + 3 ^ 40 * 2402170 * 2
def baseEnd_2402170 : Nat := 1233467823810971732527627

theorem tailTrace_2402170 : CollatzResearch.WordTrace tailWord_2402170 prefixEnd_2402170 1233467823810971732527627 := by
  unfold tailWord_2402170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21903584426838955704700991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58409558471570548545869309 21903584426838955704700991)
  ·
    refine ⟨32855376640258433557051487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21903584426838955704700991 32855376640258433557051487)
    ·
      refine ⟨49283064960387650335577231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32855376640258433557051487 49283064960387650335577231)
      ·
        refine ⟨73924597440581475503365847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49283064960387650335577231 73924597440581475503365847)
        ·
          refine ⟨110886896160872213255048771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73924597440581475503365847 110886896160872213255048771)
          ·
            refine ⟨166330344241308319882573157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110886896160872213255048771 166330344241308319882573157)
            ·
              refine ⟨31186939545245309977982467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166330344241308319882573157 31186939545245309977982467)
              ·
                refine ⟨46780409317867964966973701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31186939545245309977982467 46780409317867964966973701)
                ·
                  refine ⟨8771326747100243431307569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46780409317867964966973701 8771326747100243431307569)
                  ·
                    refine ⟨6578495060325182573480677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8771326747100243431307569 6578495060325182573480677)
                    ·
                      refine ⟨1233467823810971732527627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6578495060325182573480677 1233467823810971732527627)
                      ·
                        rfl

theorem cell23_2402170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_2402170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402170 prefixEnd_2402170 := by exact prefixLift 2402170
  have htrace : WordTrace (prefixWord ++ tailWord_2402170) baseStart_2402170 baseEnd_2402170 := by
    simpa [prefixWord, tailWord_2402170, baseEnd_2402170] using wordTrace_append hprefix tailTrace_2402170
  have hstable : (prefixWord ++ tailWord_2402170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402170).length < 2 ^ (prefixWord ++ tailWord_2402170).sum := by decide
  have hdescent : baseEnd_2402170 < baseStart_2402170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402237 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2402237 : Nat := 118140960795 + 2402237 * 2 ^ 59
def prefixEnd_2402237 : Nat := 4983230072969 + 3 ^ 40 * 2402237 * 2
def baseEnd_2402237 : Nat := 1233502227014822970389819

theorem tailTrace_2402237 : CollatzResearch.WordTrace tailWord_2402237 prefixEnd_2402237 1233502227014822970389819 := by
  unfold tailWord_2402237
  simp only [CollatzResearch.WordTrace]
  refine ⟨87616781398113093261492965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58411187598742062174328643 87616781398113093261492965)
  ·
    refine ⟨16428146512146204986529931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87616781398113093261492965 16428146512146204986529931)
    ·
      refine ⟨24642219768219307479794897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16428146512146204986529931 24642219768219307479794897)
      ·
        refine ⟨18481664826164480609846173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24642219768219307479794897 18481664826164480609846173)
        ·
          refine ⟨6930624309811680228692315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18481664826164480609846173 6930624309811680228692315)
          ·
            refine ⟨10395936464717520343038473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930624309811680228692315 10395936464717520343038473)
            ·
              refine ⟨7796952348538140257278855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10395936464717520343038473 7796952348538140257278855)
              ·
                refine ⟨11695428522807210385918283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796952348538140257278855 11695428522807210385918283)
                ·
                  refine ⟨17543142784210815578877425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11695428522807210385918283 17543142784210815578877425)
                  ·
                    refine ⟨13157357088158111684158069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17543142784210815578877425 13157357088158111684158069)
                    ·
                      refine ⟨1233502227014822970389819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13157357088158111684158069 1233502227014822970389819)
                      ·
                        rfl

theorem cell23_2402237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2402237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402237 prefixEnd_2402237 := by exact prefixLift 2402237
  have htrace : WordTrace (prefixWord ++ tailWord_2402237) baseStart_2402237 baseEnd_2402237 := by
    simpa [prefixWord, tailWord_2402237, baseEnd_2402237] using wordTrace_append hprefix tailTrace_2402237
  have hstable : (prefixWord ++ tailWord_2402237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402237).length < 2 ^ (prefixWord ++ tailWord_2402237).sum := by decide
  have hdescent : baseEnd_2402237 < baseStart_2402237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402325 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2402325 : Nat := 118140960795 + 2402325 * 2 ^ 59
def prefixEnd_2402325 : Nat := 4983230072969 + 3 ^ 40 * 2402325 * 2
def baseEnd_2402325 : Nat := 411182471104139542029805

theorem tailTrace_2402325 : CollatzResearch.WordTrace tailWord_2402325 prefixEnd_2402325 411182471104139542029805 := by
  unfold tailWord_2402325
  simp only [CollatzResearch.WordTrace]
  refine ⟨87619991021794284290696429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58413327347862856193797619 87619991021794284290696429)
  ·
    refine ⟨32857496633172856609011161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87619991021794284290696429 32857496633172856609011161)
    ·
      refine ⟨24643122474879642456758371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32857496633172856609011161 24643122474879642456758371)
      ·
        refine ⟨36964683712319463685137557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24643122474879642456758371 36964683712319463685137557)
        ·
          refine ⟨1732719549014974860240823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36964683712319463685137557 1732719549014974860240823)
          ·
            refine ⟨2599079323522462290361235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732719549014974860240823 2599079323522462290361235)
            ·
              refine ⟨3898618985283693435541853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599079323522462290361235 3898618985283693435541853)
              ·
                refine ⟨1461982119481385038328195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3898618985283693435541853 1461982119481385038328195)
                ·
                  refine ⟨2192973179222077557492293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461982119481385038328195 2192973179222077557492293)
                  ·
                    refine ⟨411182471104139542029805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192973179222077557492293 411182471104139542029805)
                    ·
                      rfl

theorem cell23_2402325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2402325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402325 prefixEnd_2402325 := by exact prefixLift 2402325
  have htrace : WordTrace (prefixWord ++ tailWord_2402325) baseStart_2402325 baseEnd_2402325 := by
    simpa [prefixWord, tailWord_2402325, baseEnd_2402325] using wordTrace_append hprefix tailTrace_2402325
  have hstable : (prefixWord ++ tailWord_2402325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402325).length < 2 ^ (prefixWord ++ tailWord_2402325).sum := by decide
  have hdescent : baseEnd_2402325 < baseStart_2402325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 1, 1, 3]
def baseStart_2402331 : Nat := 118140960795 + 2402331 * 2 ^ 59
def prefixEnd_2402331 : Nat := 4983230072969 + 3 ^ 40 * 2402331 * 2
def baseEnd_2402331 : Nat := 1233550494196345602614387

theorem tailTrace_2402331 : CollatzResearch.WordTrace tailWord_2402331 prefixEnd_2402331 1233550494196345602614387 := by
  unfold tailWord_2402331
  simp only [CollatzResearch.WordTrace]
  refine ⟨87620209859772547315414847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58413473239848364876943231 87620209859772547315414847)
  ·
    refine ⟨131430314789658820973122271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87620209859772547315414847 131430314789658820973122271)
    ·
      refine ⟨197145472184488231459683407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131430314789658820973122271 197145472184488231459683407)
      ·
        refine ⟨295718208276732347189525111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197145472184488231459683407 295718208276732347189525111)
        ·
          refine ⟨443577312415098520784287667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295718208276732347189525111 443577312415098520784287667)
          ·
            refine ⟨665365968622647781176431501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443577312415098520784287667 665365968622647781176431501)
            ·
              refine ⟨249512238233492917941161813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665365968622647781176431501 249512238233492917941161813)
              ·
                refine ⟨1461985770899372566061495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 249512238233492917941161813 1461985770899372566061495)
                ·
                  refine ⟨2192978656349058849092243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461985770899372566061495 2192978656349058849092243)
                  ·
                    refine ⟨3289467984523588273638365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192978656349058849092243 3289467984523588273638365)
                    ·
                      refine ⟨1233550494196345602614387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289467984523588273638365 1233550494196345602614387)
                      ·
                        rfl

theorem cell23_2402331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 1, 3].length) (baseStart_2402331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402331 prefixEnd_2402331 := by exact prefixLift 2402331
  have htrace : WordTrace (prefixWord ++ tailWord_2402331) baseStart_2402331 baseEnd_2402331 := by
    simpa [prefixWord, tailWord_2402331, baseEnd_2402331] using wordTrace_append hprefix tailTrace_2402331
  have hstable : (prefixWord ++ tailWord_2402331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402331).length < 2 ^ (prefixWord ++ tailWord_2402331).sum := by decide
  have hdescent : baseEnd_2402331 < baseStart_2402331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402341 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_2402341 : Nat := 118140960795 + 2402341 * 2 ^ 59
def prefixEnd_2402341 : Nat := 4983230072969 + 3 ^ 40 * 2402341 * 2
def baseEnd_2402341 : Nat := 1233555629002890563489341

theorem tailTrace_2402341 : CollatzResearch.WordTrace tailWord_2402341 prefixEnd_2402341 1233555629002890563489341 := by
  unfold tailWord_2402341
  simp only [CollatzResearch.WordTrace]
  refine ⟨87620574589736319023278877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58413716393157546015519251 87620574589736319023278877)
  ·
    refine ⟨32857715471151119633729579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87620574589736319023278877 32857715471151119633729579)
    ·
      refine ⟨49286573206726679450594369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32857715471151119633729579 49286573206726679450594369)
      ·
        refine ⟨36964929905045009587945777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49286573206726679450594369 36964929905045009587945777)
        ·
          refine ⟨27723697428783757190959333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36964929905045009587945777 27723697428783757190959333)
          ·
            refine ⟨5198193267896954473304875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27723697428783757190959333 5198193267896954473304875)
            ·
              refine ⟨7797289901845431709957313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5198193267896954473304875 7797289901845431709957313)
              ·
                refine ⟨5847967426384073782467985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7797289901845431709957313 5847967426384073782467985)
                ·
                  refine ⟨4385975569788055336850989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5847967426384073782467985 4385975569788055336850989)
                  ·
                    refine ⟨1644740838670520751319121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4385975569788055336850989 1644740838670520751319121)
                    ·
                      refine ⟨1233555629002890563489341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644740838670520751319121 1233555629002890563489341)
                      ·
                        rfl

theorem cell23_2402341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_2402341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402341 prefixEnd_2402341 := by exact prefixLift 2402341
  have htrace : WordTrace (prefixWord ++ tailWord_2402341) baseStart_2402341 baseEnd_2402341 := by
    simpa [prefixWord, tailWord_2402341, baseEnd_2402341] using wordTrace_append hprefix tailTrace_2402341
  have hstable : (prefixWord ++ tailWord_2402341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402341).length < 2 ^ (prefixWord ++ tailWord_2402341).sum := by decide
  have hdescent : baseEnd_2402341 < baseStart_2402341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402367 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_2402367 : Nat := 118140960795 + 2402367 * 2 ^ 59
def prefixEnd_2402367 : Nat := 4983230072969 + 3 ^ 40 * 2402367 * 2
def baseEnd_2402367 : Nat := 1233568979499907461764221

theorem tailTrace_2402367 : CollatzResearch.WordTrace tailWord_2402367 prefixEnd_2402367 1233568979499907461764221 := by
  unfold tailWord_2402367
  simp only [CollatzResearch.WordTrace]
  refine ⟨87621522887642125463725355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58414348591761416975816903 87621522887642125463725355)
  ·
    refine ⟨131432284331463188195588033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87621522887642125463725355 131432284331463188195588033)
    ·
      refine ⟨98574213248597391146691025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131432284331463188195588033 98574213248597391146691025)
      ·
        refine ⟨73930659936448043360018269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98574213248597391146691025 73930659936448043360018269)
        ·
          refine ⟨27723997476168016260006851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73930659936448043360018269 27723997476168016260006851)
          ·
            refine ⟨41585996214252024390010277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27723997476168016260006851 41585996214252024390010277)
            ·
              refine ⟨7797374290172254573126927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41585996214252024390010277 7797374290172254573126927)
              ·
                refine ⟨11696061435258381859690391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7797374290172254573126927 11696061435258381859690391)
                ·
                  refine ⟨17544092152887572789535587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11696061435258381859690391 17544092152887572789535587)
                  ·
                    refine ⟨26316138229331359184303381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17544092152887572789535587 26316138229331359184303381)
                    ·
                      refine ⟨1233568979499907461764221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26316138229331359184303381 1233568979499907461764221)
                      ·
                        rfl

theorem cell23_2402367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_2402367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402367 prefixEnd_2402367 := by exact prefixLift 2402367
  have htrace : WordTrace (prefixWord ++ tailWord_2402367) baseStart_2402367 baseEnd_2402367 := by
    simpa [prefixWord, tailWord_2402367, baseEnd_2402367] using wordTrace_append hprefix tailTrace_2402367
  have hstable : (prefixWord ++ tailWord_2402367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402367).length < 2 ^ (prefixWord ++ tailWord_2402367).sum := by decide
  have hdescent : baseEnd_2402367 < baseStart_2402367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402387 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3]
def baseStart_2402387 : Nat := 118140960795 + 2402387 * 2 ^ 59
def prefixEnd_2402387 : Nat := 4983230072969 + 3 ^ 40 * 2402387 * 2
def baseEnd_2402387 : Nat := 1233579249112997383514129

theorem tailTrace_2402387 : CollatzResearch.WordTrace tailWord_2402387 prefixEnd_2402387 1233579249112997383514129 := by
  unfold tailWord_2402387
  simp only [CollatzResearch.WordTrace]
  refine ⟨87622252347569668879453415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58414834898379779252968943 87622252347569668879453415)
  ·
    refine ⟨131433378521354503319180123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87622252347569668879453415 131433378521354503319180123)
    ·
      refine ⟨197150067782031754978770185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131433378521354503319180123 197150067782031754978770185)
      ·
        refine ⟨147862550836523816234077639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197150067782031754978770185 147862550836523816234077639)
        ·
          refine ⟨221793826254785724351116459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147862550836523816234077639 221793826254785724351116459)
          ·
            refine ⟨332690739382178586526674689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221793826254785724351116459 332690739382178586526674689)
            ·
              refine ⟨249518054536633939895006017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332690739382178586526674689 249518054536633939895006017)
              ·
                refine ⟨187138540902475454921254513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249518054536633939895006017 187138540902475454921254513)
                ·
                  refine ⟨140353905676856591190940885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187138540902475454921254513 140353905676856591190940885)
                  ·
                    refine ⟨3289544664301326356037677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140353905676856591190940885 3289544664301326356037677)
                    ·
                      refine ⟨1233579249112997383514129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289544664301326356037677 1233579249112997383514129)
                      ·
                        rfl

theorem cell23_2402387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_2402387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402387 prefixEnd_2402387 := by exact prefixLift 2402387
  have htrace : WordTrace (prefixWord ++ tailWord_2402387) baseStart_2402387 baseEnd_2402387 := by
    simpa [prefixWord, tailWord_2402387, baseEnd_2402387] using wordTrace_append hprefix tailTrace_2402387
  have hstable : (prefixWord ++ tailWord_2402387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402387).length < 2 ^ (prefixWord ++ tailWord_2402387).sum := by decide
  have hdescent : baseEnd_2402387 < baseStart_2402387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402405 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 1, 2, 2]
def baseStart_2402405 : Nat := 118140960795 + 2402405 * 2 ^ 59
def prefixEnd_2402405 : Nat := 4983230072969 + 3 ^ 40 * 2402405 * 2
def baseEnd_2402405 : Nat := 1233588491764778313089047

theorem tailTrace_2402405 : CollatzResearch.WordTrace tailWord_2402405 prefixEnd_2402405 1233588491764778313089047 := by
  unfold tailWord_2402405
  simp only [CollatzResearch.WordTrace]
  refine ⟨87622908861504457953608669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58415272574336305302405779 87622908861504457953608669)
  ·
    refine ⟨32858590823064171732603251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87622908861504457953608669 32858590823064171732603251)
    ·
      refine ⟨49287886234596257598904877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32858590823064171732603251 49287886234596257598904877)
      ·
        refine ⟨18482957337973596599589329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49287886234596257598904877 18482957337973596599589329)
        ·
          refine ⟨13862218003480197449691997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18482957337973596599589329 13862218003480197449691997)
          ·
            refine ⟨5198331751305074043634499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13862218003480197449691997 5198331751305074043634499)
            ·
              refine ⟨7797497626957611065451749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5198331751305074043634499 7797497626957611065451749)
              ·
                refine ⟨1462030805054552074772203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7797497626957611065451749 1462030805054552074772203)
                ·
                  refine ⟨2193046207581828112158305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462030805054552074772203 2193046207581828112158305)
                  ·
                    refine ⟨1644784655686371084118729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2193046207581828112158305 1644784655686371084118729)
                    ·
                      refine ⟨1233588491764778313089047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1644784655686371084118729 1233588491764778313089047)
                      ·
                        rfl

theorem cell23_2402405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_2402405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402405 prefixEnd_2402405 := by exact prefixLift 2402405
  have htrace : WordTrace (prefixWord ++ tailWord_2402405) baseStart_2402405 baseEnd_2402405 := by
    simpa [prefixWord, tailWord_2402405, baseEnd_2402405] using wordTrace_append hprefix tailTrace_2402405
  have hstable : (prefixWord ++ tailWord_2402405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402405).length < 2 ^ (prefixWord ++ tailWord_2402405).sum := by decide
  have hdescent : baseEnd_2402405 < baseStart_2402405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402407 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2402407 : Nat := 118140960795 + 2402407 * 2 ^ 59
def prefixEnd_2402407 : Nat := 4983230072969 + 3 ^ 40 * 2402407 * 2
def baseEnd_2402407 : Nat := 411196506242029101754679

theorem tailTrace_2402407 : CollatzResearch.WordTrace tailWord_2402407 prefixEnd_2402407 411196506242029101754679 := by
  unfold tailWord_2402407
  simp only [CollatzResearch.WordTrace]
  refine ⟨87622981807497212295181475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58415321204998141530120983 87622981807497212295181475)
  ·
    refine ⟨131434472711245818442772213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87622981807497212295181475 131434472711245818442772213)
    ·
      refine ⟨12321981816679295479009895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131434472711245818442772213 12321981816679295479009895)
      ·
        refine ⟨18482972725018943218514843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321981816679295479009895 18482972725018943218514843)
        ·
          refine ⟨27724459087528414827772265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18482972725018943218514843 27724459087528414827772265)
          ·
            refine ⟨20793344315646311120829199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27724459087528414827772265 20793344315646311120829199)
            ·
              refine ⟨31190016473469466681243799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20793344315646311120829199 31190016473469466681243799)
              ·
                refine ⟨46785024710204200021865699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31190016473469466681243799 46785024710204200021865699)
                ·
                  refine ⟨70177537065306300032798549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46785024710204200021865699 70177537065306300032798549)
                  ·
                    refine ⟨411196506242029101754679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 70177537065306300032798549 411196506242029101754679)
                    ·
                      rfl

theorem cell23_2402407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2402407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402407 prefixEnd_2402407 := by exact prefixLift 2402407
  have htrace : WordTrace (prefixWord ++ tailWord_2402407) baseStart_2402407 baseEnd_2402407 := by
    simpa [prefixWord, tailWord_2402407, baseEnd_2402407] using wordTrace_append hprefix tailTrace_2402407
  have hstable : (prefixWord ++ tailWord_2402407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402407).length < 2 ^ (prefixWord ++ tailWord_2402407).sum := by decide
  have hdescent : baseEnd_2402407 < baseStart_2402407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402455 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2402455 : Nat := 118140960795 + 2402455 * 2 ^ 59
def prefixEnd_2402455 : Nat := 4983230072969 + 3 ^ 40 * 2402455 * 2
def baseEnd_2402455 : Nat := 1233614165797503117463817

theorem tailTrace_2402455 : CollatzResearch.WordTrace tailWord_2402455 prefixEnd_2402455 1233614165797503117463817 := by
  unfold tailWord_2402455
  simp only [CollatzResearch.WordTrace]
  refine ⟨87624732511323316492928819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58416488340882210995285879 87624732511323316492928819)
  ·
    refine ⟨131437098766984974739393229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87624732511323316492928819 131437098766984974739393229)
    ·
      refine ⟨49288912037619365527272461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131437098766984974739393229 49288912037619365527272461)
      ·
        refine ⟨18483342014107262072727173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49288912037619365527272461 18483342014107262072727173)
        ·
          refine ⟨3465626627645111638636345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18483342014107262072727173 3465626627645111638636345)
          ·
            refine ⟨2599219970733833728977259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465626627645111638636345 2599219970733833728977259)
            ·
              refine ⟨3898829956100750593465889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599219970733833728977259 3898829956100750593465889)
              ·
                refine ⟨2924122467075562945099417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898829956100750593465889 2924122467075562945099417)
                ·
                  refine ⟨2193091850306672208824563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2924122467075562945099417 2193091850306672208824563)
                  ·
                    refine ⟨3289637775460008313236845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2193091850306672208824563 3289637775460008313236845)
                    ·
                      refine ⟨1233614165797503117463817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289637775460008313236845 1233614165797503117463817)
                      ·
                        rfl

theorem cell23_2402455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2402455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402455 prefixEnd_2402455 := by exact prefixLift 2402455
  have htrace : WordTrace (prefixWord ++ tailWord_2402455) baseStart_2402455 baseEnd_2402455 := by
    simpa [prefixWord, tailWord_2402455, baseEnd_2402455] using wordTrace_append hprefix tailTrace_2402455
  have hstable : (prefixWord ++ tailWord_2402455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402455).length < 2 ^ (prefixWord ++ tailWord_2402455).sum := by decide
  have hdescent : baseEnd_2402455 < baseStart_2402455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402498 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2402498 : Nat := 118140960795 + 2402498 * 2 ^ 59
def prefixEnd_2402498 : Nat := 4983230072969 + 3 ^ 40 * 2402498 * 2
def baseEnd_2402498 : Nat := 1233636245465646449226119

theorem tailTrace_2402498 : CollatzResearch.WordTrace tailWord_2402498 prefixEnd_2402498 1233636245465646449226119 := by
  unfold tailWord_2402498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906575212541883709186037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58417533900111689891162765 21906575212541883709186037)
  ·
    refine ⟨2053741426175801597736191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21906575212541883709186037 2053741426175801597736191)
    ·
      refine ⟨3080612139263702396604287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053741426175801597736191 3080612139263702396604287)
      ·
        refine ⟨4620918208895553594906431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080612139263702396604287 4620918208895553594906431)
        ·
          refine ⟨6931377313343330392359647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620918208895553594906431 6931377313343330392359647)
          ·
            refine ⟨10397065970014995588539471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931377313343330392359647 10397065970014995588539471)
            ·
              refine ⟨15595598955022493382809207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10397065970014995588539471 15595598955022493382809207)
              ·
                refine ⟨23393398432533740074213811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15595598955022493382809207 23393398432533740074213811)
                ·
                  refine ⟨35090097648800610111320717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23393398432533740074213811 35090097648800610111320717)
                  ·
                    refine ⟨13158786618300228791745269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35090097648800610111320717 13158786618300228791745269)
                    ·
                      refine ⟨1233636245465646449226119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13158786618300228791745269 1233636245465646449226119)
                      ·
                        rfl

theorem cell23_2402498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2402498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402498 prefixEnd_2402498 := by exact prefixLift 2402498
  have htrace : WordTrace (prefixWord ++ tailWord_2402498) baseStart_2402498 baseEnd_2402498 := by
    simpa [prefixWord, tailWord_2402498, baseEnd_2402498] using wordTrace_append hprefix tailTrace_2402498
  have hstable : (prefixWord ++ tailWord_2402498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402498).length < 2 ^ (prefixWord ++ tailWord_2402498).sum := by decide
  have hdescent : baseEnd_2402498 < baseStart_2402498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402501 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 5]
def baseStart_2402501 : Nat := 118140960795 + 2402501 * 2 ^ 59
def prefixEnd_2402501 : Nat := 4983230072969 + 3 ^ 40 * 2402501 * 2
def baseEnd_2402501 : Nat := 137070865100845548609845

theorem tailTrace_2402501 : CollatzResearch.WordTrace tailWord_2402501 prefixEnd_2402501 137070865100845548609845 := by
  unfold tailWord_2402501
  simp only [CollatzResearch.WordTrace]
  refine ⟨87626410269156666349103357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58417606846104444232735571 87626410269156666349103357)
  ·
    refine ⟨32859903850933749880913759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87626410269156666349103357 32859903850933749880913759)
    ·
      refine ⟨49289855776400624821370639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32859903850933749880913759 49289855776400624821370639)
      ·
        refine ⟨73934783664600937232055959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49289855776400624821370639 73934783664600937232055959)
        ·
          refine ⟨110902175496901405848083939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73934783664600937232055959 110902175496901405848083939)
          ·
            refine ⟨166353263245352108772125909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110902175496901405848083939 166353263245352108772125909)
            ·
              refine ⟨3898904607312940049346701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166353263245352108772125909 3898904607312940049346701)
              ·
                refine ⟨1462089227742352518505013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3898904607312940049346701 1462089227742352518505013)
                ·
                  refine ⟨137070865100845548609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462089227742352518505013 137070865100845548609845)
                  ·
                    rfl

theorem cell23_2402501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_2402501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402501 prefixEnd_2402501 := by exact prefixLift 2402501
  have htrace : WordTrace (prefixWord ++ tailWord_2402501) baseStart_2402501 baseEnd_2402501 := by
    simpa [prefixWord, tailWord_2402501, baseEnd_2402501] using wordTrace_append hprefix tailTrace_2402501
  have hstable : (prefixWord ++ tailWord_2402501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402501).length < 2 ^ (prefixWord ++ tailWord_2402501).sum := by decide
  have hdescent : baseEnd_2402501 < baseStart_2402501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402518 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2402518 : Nat := 118140960795 + 2402518 * 2 ^ 59
def prefixEnd_2402518 : Nat := 4983230072969 + 3 ^ 40 * 2402518 * 2
def baseEnd_2402518 : Nat := 137071835008748485664003

theorem tailTrace_2402518 : CollatzResearch.WordTrace tailWord_2402518 prefixEnd_2402518 137071835008748485664003 := by
  unfold tailWord_2402518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476689394380942390779513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58418020206730052168314805 5476689394380942390779513)
  ·
    refine ⟨4107517045785706793084635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5476689394380942390779513 4107517045785706793084635)
    ·
      refine ⟨6161275568678560189626953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107517045785706793084635 6161275568678560189626953)
      ·
        refine ⟨4620956676508920142220215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6161275568678560189626953 4620956676508920142220215)
        ·
          refine ⟨6931435014763380213330323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620956676508920142220215 6931435014763380213330323)
          ·
            refine ⟨10397152522145070319995485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931435014763380213330323 10397152522145070319995485)
            ·
              refine ⟨3898932195804401369998307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10397152522145070319995485 3898932195804401369998307)
              ·
                refine ⟨5848398293706602054997461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898932195804401369998307 5848398293706602054997461)
                ·
                  refine ⟨137071835008748485664003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5848398293706602054997461 137071835008748485664003)
                  ·
                    rfl

theorem cell23_2402518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2402518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402518 prefixEnd_2402518 := by exact prefixLift 2402518
  have htrace : WordTrace (prefixWord ++ tailWord_2402518) baseStart_2402518 baseEnd_2402518 := by
    simpa [prefixWord, tailWord_2402518, baseEnd_2402518] using wordTrace_append hprefix tailTrace_2402518
  have hstable : (prefixWord ++ tailWord_2402518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402518).length < 2 ^ (prefixWord ++ tailWord_2402518).sum := by decide
  have hdescent : baseEnd_2402518 < baseStart_2402518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402571 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3]
def baseStart_2402571 : Nat := 118140960795 + 2402571 * 2 ^ 59
def prefixEnd_2402571 : Nat := 4983230072969 + 3 ^ 40 * 2402571 * 2
def baseEnd_2402571 : Nat := 1233673729553424663613283

theorem tailTrace_2402571 : CollatzResearch.WordTrace tailWord_2402571 prefixEnd_2402571 1233673729553424663613283 := by
  unfold tailWord_2402571
  simp only [CollatzResearch.WordTrace]
  refine ⟨87628963378903068304151567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58419308919268712202767711 87628963378903068304151567)
  ·
    refine ⟨131443445068354602456227351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87628963378903068304151567 131443445068354602456227351)
    ·
      refine ⟨197165167602531903684341027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131443445068354602456227351 197165167602531903684341027)
      ·
        refine ⟨295747751403797855526511541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197165167602531903684341027 295747751403797855526511541)
        ·
          refine ⟨27726351694106048955610457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295747751403797855526511541 27726351694106048955610457)
          ·
            refine ⟨20794763770579536716707843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27726351694106048955610457 20794763770579536716707843)
            ·
              refine ⟨31192145655869305075061765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20794763770579536716707843 31192145655869305075061765)
              ·
                refine ⟨5848527310475494701574081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31192145655869305075061765 5848527310475494701574081)
                ·
                  refine ⟨4386395482856621026180561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5848527310475494701574081 4386395482856621026180561)
                  ·
                    refine ⟨3289796612142465769635421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4386395482856621026180561 3289796612142465769635421)
                    ·
                      refine ⟨1233673729553424663613283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289796612142465769635421 1233673729553424663613283)
                      ·
                        rfl

theorem cell23_2402571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3].length) (baseStart_2402571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402571 prefixEnd_2402571 := by exact prefixLift 2402571
  have htrace : WordTrace (prefixWord ++ tailWord_2402571) baseStart_2402571 baseEnd_2402571 := by
    simpa [prefixWord, tailWord_2402571, baseEnd_2402571] using wordTrace_append hprefix tailTrace_2402571
  have hstable : (prefixWord ++ tailWord_2402571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402571).length < 2 ^ (prefixWord ++ tailWord_2402571).sum := by decide
  have hdescent : baseEnd_2402571 < baseStart_2402571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402591 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 6]
def baseStart_2402591 : Nat := 118140960795 + 2402591 * 2 ^ 59
def prefixEnd_2402591 : Nat := 4983230072969 + 3 ^ 40 * 2402591 * 2
def baseEnd_2402591 : Nat := 137075999907390509484799

theorem tailTrace_2402591 : CollatzResearch.WordTrace tailWord_2402591 prefixEnd_2402591 137075999907390509484799 := by
  unfold tailWord_2402591
  simp only [CollatzResearch.WordTrace]
  refine ⟨87629692838830611719879627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58419795225887074479919751 87629692838830611719879627)
  ·
    refine ⟨131444539258245917579819441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87629692838830611719879627 131444539258245917579819441)
    ·
      refine ⟨98583404443684438184864581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131444539258245917579819441 98583404443684438184864581)
      ·
        refine ⟨18484388333190832159662109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98583404443684438184864581 18484388333190832159662109)
        ·
          refine ⟨6931645624946562059873291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18484388333190832159662109 6931645624946562059873291)
          ·
            refine ⟨10397468437419843089809937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931645624946562059873291 10397468437419843089809937)
            ·
              refine ⟨7798101328064882317357453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397468437419843089809937 7798101328064882317357453)
              ·
                refine ⟨2924287998024330869009045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7798101328064882317357453 2924287998024330869009045)
                ·
                  refine ⟨137075999907390509484799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2924287998024330869009045 137075999907390509484799)
                  ·
                    rfl

theorem cell23_2402591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 6].length) (baseStart_2402591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402591 prefixEnd_2402591 := by exact prefixLift 2402591
  have htrace : WordTrace (prefixWord ++ tailWord_2402591) baseStart_2402591 baseEnd_2402591 := by
    simpa [prefixWord, tailWord_2402591, baseEnd_2402591] using wordTrace_append hprefix tailTrace_2402591
  have hstable : (prefixWord ++ tailWord_2402591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402591).length < 2 ^ (prefixWord ++ tailWord_2402591).sum := by decide
  have hdescent : baseEnd_2402591 < baseStart_2402591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402599 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2402599 : Nat := 118140960795 + 2402599 * 2 ^ 59
def prefixEnd_2402599 : Nat := 4983230072969 + 3 ^ 40 * 2402599 * 2
def baseEnd_2402599 : Nat := 411229369003916851354385

theorem tailTrace_2402599 : CollatzResearch.WordTrace tailWord_2402599 prefixEnd_2402599 411229369003916851354385 := by
  unfold tailWord_2402599
  simp only [CollatzResearch.WordTrace]
  refine ⟨87629984622801629086170851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58419989748534419390780567 87629984622801629086170851)
  ·
    refine ⟨131444976934202443629256277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87629984622801629086170851 131444976934202443629256277)
    ·
      refine ⟨1540370823447684886280347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 131444976934202443629256277 1540370823447684886280347)
      ·
        refine ⟨2310556235171527329420521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540370823447684886280347 2310556235171527329420521)
        ·
          refine ⟨1732917176378645497065391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2310556235171527329420521 1732917176378645497065391)
          ·
            refine ⟨2599375764567968245598087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732917176378645497065391 2599375764567968245598087)
            ·
              refine ⟨3899063646851952368397131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599375764567968245598087 3899063646851952368397131)
              ·
                refine ⟨5848595470277928552595697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899063646851952368397131 5848595470277928552595697)
                ·
                  refine ⟨4386446602708446414446773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5848595470277928552595697 4386446602708446414446773)
                  ·
                    refine ⟨411229369003916851354385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4386446602708446414446773 411229369003916851354385)
                    ·
                      rfl

theorem cell23_2402599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2402599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402599 prefixEnd_2402599 := by exact prefixLift 2402599
  have htrace : WordTrace (prefixWord ++ tailWord_2402599) baseStart_2402599 baseEnd_2402599 := by
    simpa [prefixWord, tailWord_2402599, baseEnd_2402599] using wordTrace_append hprefix tailTrace_2402599
  have hstable : (prefixWord ++ tailWord_2402599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402599).length < 2 ^ (prefixWord ++ tailWord_2402599).sum := by decide
  have hdescent : baseEnd_2402599 < baseStart_2402599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402602 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2402602 : Nat := 118140960795 + 2402602 * 2 ^ 59
def prefixEnd_2402602 : Nat := 4983230072969 + 3 ^ 40 * 2402602 * 2
def baseEnd_2402602 : Nat := 1233689647453714042325641

theorem tailTrace_2402602 : CollatzResearch.WordTrace tailWord_2402602 prefixEnd_2402602 1233689647453714042325641 := by
  unfold tailWord_2402602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21907523510447690149632515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58420062694527173732353373 21907523510447690149632515)
  ·
    refine ⟨32861285265671535224448773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21907523510447690149632515 32861285265671535224448773)
    ·
      refine ⟨6161490987313412854584145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32861285265671535224448773 6161490987313412854584145)
      ·
        refine ⟨4621118240485059640938109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6161490987313412854584145 4621118240485059640938109)
        ·
          refine ⟨1732919340181897365351791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4621118240485059640938109 1732919340181897365351791)
          ·
            refine ⟨2599379010272846048027687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732919340181897365351791 2599379010272846048027687)
            ·
              refine ⟨3899068515409269072041531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599379010272846048027687 3899068515409269072041531)
              ·
                refine ⟨5848602773113903608062297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899068515409269072041531 5848602773113903608062297)
                ·
                  refine ⟨4386452079835427706046723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5848602773113903608062297 4386452079835427706046723)
                  ·
                    refine ⟨6579678119753141559070085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4386452079835427706046723 6579678119753141559070085)
                    ·
                      refine ⟨1233689647453714042325641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6579678119753141559070085 1233689647453714042325641)
                      ·
                        rfl

theorem cell23_2402602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2402602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402602 prefixEnd_2402602 := by exact prefixLift 2402602
  have htrace : WordTrace (prefixWord ++ tailWord_2402602) baseStart_2402602 baseEnd_2402602 := by
    simpa [prefixWord, tailWord_2402602, baseEnd_2402602] using wordTrace_append hprefix tailTrace_2402602
  have hstable : (prefixWord ++ tailWord_2402602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402602).length < 2 ^ (prefixWord ++ tailWord_2402602).sum := by decide
  have hdescent : baseEnd_2402602 < baseStart_2402602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402605 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2402605 : Nat := 118140960795 + 2402605 * 2 ^ 59
def prefixEnd_2402605 : Nat := 4983230072969 + 3 ^ 40 * 2402605 * 2
def baseEnd_2402605 : Nat := 1233691187895677530588127

theorem tailTrace_2402605 : CollatzResearch.WordTrace tailWord_2402605 prefixEnd_2402605 1233691187895677530588127 := by
  unfold tailWord_2402605
  simp only [CollatzResearch.WordTrace]
  refine ⟨87630203460779892110889269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58420135640519928073926179 87630203460779892110889269)
  ·
    refine ⟨8215331574448114885395869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87630203460779892110889269 8215331574448114885395869)
    ·
      refine ⟨3080749340418043082023451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8215331574448114885395869 3080749340418043082023451)
      ·
        refine ⟨4621124010627064623035177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3080749340418043082023451 4621124010627064623035177)
        ·
          refine ⟨3465843007970298467276383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4621124010627064623035177 3465843007970298467276383)
          ·
            refine ⟨5198764511955447700914575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465843007970298467276383 5198764511955447700914575)
            ·
              refine ⟨7798146767933171551371863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5198764511955447700914575 7798146767933171551371863)
              ·
                refine ⟨11697220151899757327057795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7798146767933171551371863 11697220151899757327057795)
                ·
                  refine ⟨17545830227849635990586693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11697220151899757327057795 17545830227849635990586693)
                  ·
                    refine ⟨3289843167721806748235005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17545830227849635990586693 3289843167721806748235005)
                    ·
                      refine ⟨1233691187895677530588127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289843167721806748235005 1233691187895677530588127)
                      ·
                        rfl

theorem cell23_2402605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2402605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402605 prefixEnd_2402605 := by exact prefixLift 2402605
  have htrace : WordTrace (prefixWord ++ tailWord_2402605) baseStart_2402605 baseEnd_2402605 := by
    simpa [prefixWord, tailWord_2402605, baseEnd_2402605] using wordTrace_append hprefix tailTrace_2402605
  have hstable : (prefixWord ++ tailWord_2402605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402605).length < 2 ^ (prefixWord ++ tailWord_2402605).sum := by decide
  have hdescent : baseEnd_2402605 < baseStart_2402605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402612 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2402612 : Nat := 118140960795 + 2402612 * 2 ^ 59
def prefixEnd_2402612 : Nat := 4983230072969 + 3 ^ 40 * 2402612 * 2
def baseEnd_2402612 : Nat := 411231594086753001066865

theorem tailTrace_2402612 : CollatzResearch.WordTrace tailWord_2402612 prefixEnd_2402612 411231594086753001066865 := by
  unfold tailWord_2402612
  simp only [CollatzResearch.WordTrace]
  refine ⟨43815229385877266153197045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58420305847836354870929393 43815229385877266153197045)
  ·
    refine ⟨4107677754925993701862223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43815229385877266153197045 4107677754925993701862223)
    ·
      refine ⟨6161516632388990552793335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107677754925993701862223 6161516632388990552793335)
      ·
        refine ⟨9242274948583485829190003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161516632388990552793335 9242274948583485829190003)
        ·
          refine ⟨13863412422875228743785005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242274948583485829190003 13863412422875228743785005)
          ·
            refine ⟨5198779658578210778919377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13863412422875228743785005 5198779658578210778919377)
            ·
              refine ⟨3899084743933658084189533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198779658578210778919377 3899084743933658084189533)
              ·
                refine ⟨1462156778975121781571075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3899084743933658084189533 1462156778975121781571075)
                ·
                  refine ⟨2193235168462682672356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462156778975121781571075 2193235168462682672356613)
                  ·
                    refine ⟨411231594086753001066865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193235168462682672356613 411231594086753001066865)
                    ·
                      rfl

theorem cell23_2402612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2402612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402612 prefixEnd_2402612 := by exact prefixLift 2402612
  have htrace : WordTrace (prefixWord ++ tailWord_2402612) baseStart_2402612 baseEnd_2402612 := by
    simpa [prefixWord, tailWord_2402612, baseEnd_2402612] using wordTrace_append hprefix tailTrace_2402612
  have hstable : (prefixWord ++ tailWord_2402612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402612).length < 2 ^ (prefixWord ++ tailWord_2402612).sum := by decide
  have hdescent : baseEnd_2402612 < baseStart_2402612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402625 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 6]
def baseStart_2402625 : Nat := 118140960795 + 2402625 * 2 ^ 59
def prefixEnd_2402625 : Nat := 4983230072969 + 3 ^ 40 * 2402625 * 2
def baseEnd_2402625 : Nat := 137077939723196383593115

theorem tailTrace_2402625 : CollatzResearch.WordTrace tailWord_2402625 prefixEnd_2402625 137077939723196383593115 := by
  unfold tailWord_2402625
  simp only [CollatzResearch.WordTrace]
  refine ⟨87630932920707435526617329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58420621947138290351078219 87630932920707435526617329)
  ·
    refine ⟨65723199690530576644962997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87630932920707435526617329 65723199690530576644962997)
    ·
      refine ⟨6161549970987241560465281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65723199690530576644962997 6161549970987241560465281)
      ·
        refine ⟨4621162478240431170348961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6161549970987241560465281 4621162478240431170348961)
        ·
          refine ⟨3465871858680323377761721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4621162478240431170348961 3465871858680323377761721)
          ·
            refine ⟨2599403894010242533321291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465871858680323377761721 2599403894010242533321291)
            ·
              refine ⟨3899105841015363799981937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599403894010242533321291 3899105841015363799981937)
              ·
                refine ⟨2924329380761522849986453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899105841015363799981937 2924329380761522849986453)
                ·
                  refine ⟨137077939723196383593115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2924329380761522849986453 137077939723196383593115)
                  ·
                    rfl

theorem cell23_2402625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_2402625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402625 prefixEnd_2402625 := by exact prefixLift 2402625
  have htrace : WordTrace (prefixWord ++ tailWord_2402625) baseStart_2402625 baseEnd_2402625 := by
    simpa [prefixWord, tailWord_2402625, baseEnd_2402625] using wordTrace_append hprefix tailTrace_2402625
  have hstable : (prefixWord ++ tailWord_2402625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402625).length < 2 ^ (prefixWord ++ tailWord_2402625).sum := by decide
  have hdescent : baseEnd_2402625 < baseStart_2402625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402634 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_2402634 : Nat := 118140960795 + 2402634 * 2 ^ 59
def prefixEnd_2402634 : Nat := 4983230072969 + 3 ^ 40 * 2402634 * 2
def baseEnd_2402634 : Nat := 411235359611552639041831

theorem tailTrace_2402634 : CollatzResearch.WordTrace tailWord_2402634 prefixEnd_2402634 411235359611552639041831 := by
  unfold tailWord_2402634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21907815294418707515923739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58420840785116553375796637 21907815294418707515923739)
  ·
    refine ⟨32861722941628061273885609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21907815294418707515923739 32861722941628061273885609)
    ·
      refine ⟨24646292206221045955414207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32861722941628061273885609 24646292206221045955414207)
      ·
        refine ⟨36969438309331568933121311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24646292206221045955414207 36969438309331568933121311)
        ·
          refine ⟨55454157463997353399681967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36969438309331568933121311 55454157463997353399681967)
          ·
            refine ⟨83181236195996030099522951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55454157463997353399681967 83181236195996030099522951)
            ·
              refine ⟨124771854293994045149284427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83181236195996030099522951 124771854293994045149284427)
              ·
                refine ⟨187157781440991067723926641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124771854293994045149284427 187157781440991067723926641)
                ·
                  refine ⟨140368336080743300792944981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187157781440991067723926641 140368336080743300792944981)
                  ·
                    refine ⟨411235359611552639041831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 140368336080743300792944981 411235359611552639041831)
                    ·
                      rfl

theorem cell23_2402634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_2402634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402634 prefixEnd_2402634 := by exact prefixLift 2402634
  have htrace : WordTrace (prefixWord ++ tailWord_2402634) baseStart_2402634 baseEnd_2402634 := by
    simpa [prefixWord, tailWord_2402634, baseEnd_2402634] using wordTrace_append hprefix tailTrace_2402634
  have hstable : (prefixWord ++ tailWord_2402634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402634).length < 2 ^ (prefixWord ++ tailWord_2402634).sum := by decide
  have hdescent : baseEnd_2402634 < baseStart_2402634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402702 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2402702 : Nat := 118140960795 + 2402702 * 2 ^ 59
def prefixEnd_2402702 : Nat := 4983230072969 + 3 ^ 40 * 2402702 * 2
def baseEnd_2402702 : Nat := 411246998506387883691727

theorem tailTrace_2402702 : CollatzResearch.WordTrace tailWord_2402702 prefixEnd_2402702 411246998506387883691727 := by
  unfold tailWord_2402702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954217667678559709646295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58422494227618985118113573 10954217667678559709646295)
  ·
    refine ⟨16431326501517839564469443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10954217667678559709646295 16431326501517839564469443)
    ·
      refine ⟨24646989752276759346704165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16431326501517839564469443 24646989752276759346704165)
      ·
        refine ⟨4621310578551892377507031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24646989752276759346704165 4621310578551892377507031)
        ·
          refine ⟨6931965867827838566260547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4621310578551892377507031 6931965867827838566260547)
          ·
            refine ⟨10397948801741757849390821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931965867827838566260547 10397948801741757849390821)
            ·
              refine ⟨1949615400326579596760779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10397948801741757849390821 1949615400326579596760779)
              ·
                refine ⟨2924423100489869395141169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949615400326579596760779 2924423100489869395141169)
                ·
                  refine ⟨2193317325367402046355877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2924423100489869395141169 2193317325367402046355877)
                  ·
                    refine ⟨411246998506387883691727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193317325367402046355877 411246998506387883691727)
                    ·
                      rfl

theorem cell23_2402702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2402702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402702 prefixEnd_2402702 := by exact prefixLift 2402702
  have htrace : WordTrace (prefixWord ++ tailWord_2402702) baseStart_2402702 baseEnd_2402702 := by
    simpa [prefixWord, tailWord_2402702, baseEnd_2402702] using wordTrace_append hprefix tailTrace_2402702
  have hstable : (prefixWord ++ tailWord_2402702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402702).length < 2 ^ (prefixWord ++ tailWord_2402702).sum := by decide
  have hdescent : baseEnd_2402702 < baseStart_2402702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402712 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2402712 : Nat := 118140960795 + 2402712 * 2 ^ 59
def prefixEnd_2402712 : Nat := 4983230072969 + 3 ^ 40 * 2402712 * 2
def baseEnd_2402712 : Nat := 1233746130325708611950135

theorem tailTrace_2402712 : CollatzResearch.WordTrace tailWord_2402712 prefixEnd_2402712 1233746130325708611950135 := by
  unfold tailWord_2402712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43817053035696124692517195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58422737380928166256689593 43817053035696124692517195)
  ·
    refine ⟨65725579553544187038775793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43817053035696124692517195 65725579553544187038775793)
    ·
      refine ⟨49294184665158140279081845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65725579553544187038775793 49294184665158140279081845)
      ·
        refine ⟨4621329812358575651163923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49294184665158140279081845 4621329812358575651163923)
        ·
          refine ⟨6931994718537863476745885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4621329812358575651163923 6931994718537863476745885)
          ·
            refine ⟨2599498019451698803779707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6931994718537863476745885 2599498019451698803779707)
            ·
              refine ⟨3899247029177548205669561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599498019451698803779707 3899247029177548205669561)
              ·
                refine ⟨2924435271883161154252171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899247029177548205669561 2924435271883161154252171)
                ·
                  refine ⟨4386652907824741731378257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924435271883161154252171 4386652907824741731378257)
                  ·
                    refine ⟨3289989680868556298533693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4386652907824741731378257 3289989680868556298533693)
                    ·
                      refine ⟨1233746130325708611950135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3289989680868556298533693 1233746130325708611950135)
                      ·
                        rfl

theorem cell23_2402712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2402712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402712 prefixEnd_2402712 := by exact prefixLift 2402712
  have htrace : WordTrace (prefixWord ++ tailWord_2402712) baseStart_2402712 baseEnd_2402712 := by
    simpa [prefixWord, tailWord_2402712, baseEnd_2402712] using wordTrace_append hprefix tailTrace_2402712
  have hstable : (prefixWord ++ tailWord_2402712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402712).length < 2 ^ (prefixWord ++ tailWord_2402712).sum := by decide
  have hdescent : baseEnd_2402712 < baseStart_2402712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402748 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2402748 : Nat := 118140960795 + 2402748 * 2 ^ 59
def prefixEnd_2402748 : Nat := 4983230072969 + 3 ^ 40 * 2402748 * 2
def baseEnd_2402748 : Nat := 1233764615629270471099969

theorem tailTrace_2402748 : CollatzResearch.WordTrace tailWord_2402748 prefixEnd_2402748 1233764615629270471099969 := by
  unfold tailWord_2402748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43817709549630913766672449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58423612732841218355563265 43817709549630913766672449)
  ·
    refine ⟨32863282162223185325004337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43817709549630913766672449 32863282162223185325004337)
    ·
      refine ⟨24647461621667388993753253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32863282162223185325004337 24647461621667388993753253)
      ·
        refine ⟨4621399054062635436328735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24647461621667388993753253 4621399054062635436328735)
        ·
          refine ⟨6932098581093953154493103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4621399054062635436328735 6932098581093953154493103)
          ·
            refine ⟨10398147871640929731739655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6932098581093953154493103 10398147871640929731739655)
            ·
              refine ⟨15597221807461394597609483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398147871640929731739655 15597221807461394597609483)
              ·
                refine ⟨23395832711192091896414225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15597221807461394597609483 23395832711192091896414225)
                ·
                  refine ⟨17546874533394068922310669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23395832711192091896414225 17546874533394068922310669)
                  ·
                    refine ⟨6580077950022775845866501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17546874533394068922310669 6580077950022775845866501)
                    ·
                      refine ⟨1233764615629270471099969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6580077950022775845866501 1233764615629270471099969)
                      ·
                        rfl

theorem cell23_2402748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2402748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402748 prefixEnd_2402748 := by exact prefixLift 2402748
  have htrace : WordTrace (prefixWord ++ tailWord_2402748) baseStart_2402748 baseEnd_2402748 := by
    simpa [prefixWord, tailWord_2402748, baseEnd_2402748] using wordTrace_append hprefix tailTrace_2402748
  have hstable : (prefixWord ++ tailWord_2402748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402748).length < 2 ^ (prefixWord ++ tailWord_2402748).sum := by decide
  have hdescent : baseEnd_2402748 < baseStart_2402748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402761 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_2402761 : Nat := 118140960795 + 2402761 * 2 ^ 59
def prefixEnd_2402761 : Nat := 4983230072969 + 3 ^ 40 * 2402761 * 2
def baseEnd_2402761 : Nat := 1233771290877778920237409

theorem tailTrace_2402761 : CollatzResearch.WordTrace tailWord_2402761 prefixEnd_2402761 1233771290877778920237409 := by
  unfold tailWord_2402761
  simp only [CollatzResearch.WordTrace]
  refine ⟨87635893248214730753568137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58423928832143153835712091 87635893248214730753568137)
  ·
    refine ⟨65726919936161048065176103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87635893248214730753568137 65726919936161048065176103)
    ·
      refine ⟨98590379904241572097764155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65726919936161048065176103 98590379904241572097764155)
      ·
        refine ⟨147885569856362358146646233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98590379904241572097764155 147885569856362358146646233)
        ·
          refine ⟨110914177392271768609984675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147885569856362358146646233 110914177392271768609984675)
          ·
            refine ⟨166371266088407652914977013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110914177392271768609984675 166371266088407652914977013)
            ·
              refine ⟨15597306195788217460779095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166371266088407652914977013 15597306195788217460779095)
              ·
                refine ⟨23395959293682326191168643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15597306195788217460779095 23395959293682326191168643)
                ·
                  refine ⟨35093938940523489286752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23395959293682326191168643 35093938940523489286752965)
                  ·
                    refine ⟨6580113551348154241266181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35093938940523489286752965 6580113551348154241266181)
                    ·
                      refine ⟨1233771290877778920237409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6580113551348154241266181 1233771290877778920237409)
                      ·
                        rfl

theorem cell23_2402761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_2402761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402761 prefixEnd_2402761 := by exact prefixLift 2402761
  have htrace : WordTrace (prefixWord ++ tailWord_2402761) baseStart_2402761 baseEnd_2402761 := by
    simpa [prefixWord, tailWord_2402761, baseEnd_2402761] using wordTrace_append hprefix tailTrace_2402761
  have hstable : (prefixWord ++ tailWord_2402761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402761).length < 2 ^ (prefixWord ++ tailWord_2402761).sum := by decide
  have hdescent : baseEnd_2402761 < baseStart_2402761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402786 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2402786 : Nat := 118140960795 + 2402786 * 2 ^ 59
def prefixEnd_2402786 : Nat := 4983230072969 + 3 ^ 40 * 2402786 * 2
def baseEnd_2402786 : Nat := 1233784127894141322424795

theorem tailTrace_2402786 : CollatzResearch.WordTrace tailWord_2402786 prefixEnd_2402786 1233784127894141322424795 := by
  unfold tailWord_2402786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909201268281040005807053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58424536715416106682152141 21909201268281040005807053)
  ·
    refine ⟨8215950475605390002177645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21909201268281040005807053 8215950475605390002177645)
    ·
      refine ⟨3080981428352021250816617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8215950475605390002177645 3080981428352021250816617)
      ·
        refine ⟨2310736071264015938112463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3080981428352021250816617 2310736071264015938112463)
        ·
          refine ⟨3466104106896023907168695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310736071264015938112463 3466104106896023907168695)
          ·
            refine ⟨5199156160344035860753043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466104106896023907168695 5199156160344035860753043)
            ·
              refine ⟨7798734240516053791129565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199156160344035860753043 7798734240516053791129565)
              ·
                refine ⟨2924525340193520171673587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7798734240516053791129565 2924525340193520171673587)
                ·
                  refine ⟨4386788010290280257510381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924525340193520171673587 4386788010290280257510381)
                  ·
                    refine ⟨1645045503858855096566393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4386788010290280257510381 1645045503858855096566393)
                    ·
                      refine ⟨1233784127894141322424795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645045503858855096566393 1233784127894141322424795)
                      ·
                        rfl

theorem cell23_2402786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2402786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402786 prefixEnd_2402786 := by exact prefixLift 2402786
  have htrace : WordTrace (prefixWord ++ tailWord_2402786) baseStart_2402786 baseEnd_2402786 := by
    simpa [prefixWord, tailWord_2402786, baseEnd_2402786] using wordTrace_append hprefix tailTrace_2402786
  have hstable : (prefixWord ++ tailWord_2402786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402786).length < 2 ^ (prefixWord ++ tailWord_2402786).sum := by decide
  have hdescent : baseEnd_2402786 < baseStart_2402786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402839 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 5]
def baseStart_2402839 : Nat := 118140960795 + 2402839 * 2 ^ 59
def prefixEnd_2402839 : Nat := 4983230072969 + 3 ^ 40 * 2402839 * 2
def baseEnd_2402839 : Nat := 137090149152092179451339

theorem tailTrace_2402839 : CollatzResearch.WordTrace tailWord_2402839 prefixEnd_2402839 137090149152092179451339 := by
  unfold tailWord_2402839
  simp only [CollatzResearch.WordTrace]
  refine ⟨87638738141932150074907571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58425825427954766716605047 87638738141932150074907571)
  ·
    refine ⟨131458107212898225112361357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87638738141932150074907571 131458107212898225112361357)
    ·
      refine ⟨49296790204836834417135509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131458107212898225112361357 49296790204836834417135509)
      ·
        refine ⟨2310787040851726613303227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49296790204836834417135509 2310787040851726613303227)
        ·
          refine ⟨3466180561277589919954841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310787040851726613303227 3466180561277589919954841)
          ·
            refine ⟨2599635420958192439966131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466180561277589919954841 2599635420958192439966131)
            ·
              refine ⟨3899453131437288659949197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599635420958192439966131 3899453131437288659949197)
              ·
                refine ⟨1462294924288983247480949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3899453131437288659949197 1462294924288983247480949)
                ·
                  refine ⟨137090149152092179451339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462294924288983247480949 137090149152092179451339)
                  ·
                    rfl

theorem cell23_2402839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 5].length) (baseStart_2402839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402839 prefixEnd_2402839 := by exact prefixLift 2402839
  have htrace : WordTrace (prefixWord ++ tailWord_2402839) baseStart_2402839 baseEnd_2402839 := by
    simpa [prefixWord, tailWord_2402839, baseEnd_2402839] using wordTrace_append hprefix tailTrace_2402839
  have hstable : (prefixWord ++ tailWord_2402839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402839).length < 2 ^ (prefixWord ++ tailWord_2402839).sum := by decide
  have hdescent : baseEnd_2402839 < baseStart_2402839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402852 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_2402852 : Nat := 118140960795 + 2402852 * 2 ^ 59
def prefixEnd_2402852 : Nat := 4983230072969 + 3 ^ 40 * 2402852 * 2
def baseEnd_2402852 : Nat := 411272672539112688066497

theorem tailTrace_2402852 : CollatzResearch.WordTrace tailWord_2402852 prefixEnd_2402852 411272672539112688066497 := by
  unfold tailWord_2402852
  simp only [CollatzResearch.WordTrace]
  refine ⟨43819606145442526647565405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58426141527256702196753873 43819606145442526647565405)
  ·
    refine ⟨16432352304540947492837027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43819606145442526647565405 16432352304540947492837027)
    ·
      refine ⟨24648528456811421239255541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16432352304540947492837027 24648528456811421239255541)
      ·
        refine ⟨2310799542826070741180207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24648528456811421239255541 2310799542826070741180207)
        ·
          refine ⟨3466199314239106111770311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310799542826070741180207 3466199314239106111770311)
          ·
            refine ⟨5199298971358659167655467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466199314239106111770311 5199298971358659167655467)
            ·
              refine ⟨7798948457037988751483201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199298971358659167655467 7798948457037988751483201)
              ·
                refine ⟨5849211342778491563612401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7798948457037988751483201 5849211342778491563612401)
                ·
                  refine ⟨4386908507083868672709301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849211342778491563612401 4386908507083868672709301)
                  ·
                    refine ⟨411272672539112688066497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4386908507083868672709301 411272672539112688066497)
                    ·
                      rfl

theorem cell23_2402852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_2402852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402852 prefixEnd_2402852 := by exact prefixLift 2402852
  have htrace : WordTrace (prefixWord ++ tailWord_2402852) baseStart_2402852 baseEnd_2402852 := by
    simpa [prefixWord, tailWord_2402852, baseEnd_2402852] using wordTrace_append hprefix tailTrace_2402852
  have hstable : (prefixWord ++ tailWord_2402852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402852).length < 2 ^ (prefixWord ++ tailWord_2402852).sum := by decide
  have hdescent : baseEnd_2402852 < baseStart_2402852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402865 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_2402865 : Nat := 118140960795 + 2402865 * 2 ^ 59
def prefixEnd_2402865 : Nat := 4983230072969 + 3 ^ 40 * 2402865 * 2
def baseEnd_2402865 : Nat := 411274897621948837778977

theorem tailTrace_2402865 : CollatzResearch.WordTrace tailWord_2402865 prefixEnd_2402865 411274897621948837778977 := by
  unfold tailWord_2402865
  simp only [CollatzResearch.WordTrace]
  refine ⟨87639686439837956515354049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58426457626558637676902699 87639686439837956515354049)
  ·
    refine ⟨65729764829878467386515537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87639686439837956515354049 65729764829878467386515537)
    ·
      refine ⟨49297323622408850539886653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65729764829878467386515537 49297323622408850539886653)
      ·
        refine ⟨18486496358403318952457495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49297323622408850539886653 18486496358403318952457495)
        ·
          refine ⟨27729744537604978428686243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18486496358403318952457495 27729744537604978428686243)
          ·
            refine ⟨41594616806407467643029365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27729744537604978428686243 41594616806407467643029365)
            ·
              refine ⟨3899495325600700091534003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41594616806407467643029365 3899495325600700091534003)
              ·
                refine ⟨5849242988401050137301005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899495325600700091534003 5849242988401050137301005)
                ·
                  refine ⟨2193466120650393801487877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5849242988401050137301005 2193466120650393801487877)
                  ·
                    refine ⟨411274897621948837778977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193466120650393801487877 411274897621948837778977)
                    ·
                      rfl

theorem cell23_2402865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_2402865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402865 prefixEnd_2402865 := by exact prefixLift 2402865
  have htrace : WordTrace (prefixWord ++ tailWord_2402865) baseStart_2402865 baseEnd_2402865 := by
    simpa [prefixWord, tailWord_2402865, baseEnd_2402865] using wordTrace_append hprefix tailTrace_2402865
  have hstable : (prefixWord ++ tailWord_2402865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402865).length < 2 ^ (prefixWord ++ tailWord_2402865).sum := by decide
  have hdescent : baseEnd_2402865 < baseStart_2402865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402888 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2402888 : Nat := 118140960795 + 2402888 * 2 ^ 59
def prefixEnd_2402888 : Nat := 4983230072969 + 3 ^ 40 * 2402888 * 2
def baseEnd_2402888 : Nat := 1233836502920899923349325

theorem tailTrace_2402888 : CollatzResearch.WordTrace tailWord_2402888 prefixEnd_2402888 1233836502920899923349325 := by
  unfold tailWord_2402888
  simp only [CollatzResearch.WordTrace]
  refine ⟨43820262659377315721720659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58427016879169754295627545 43820262659377315721720659)
  ·
    refine ⟨65730393989065973582580989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43820262659377315721720659 65730393989065973582580989)
    ·
      refine ⟨24648897745899740093467871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65730393989065973582580989 24648897745899740093467871)
      ·
        refine ⟨36973346618849610140201807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24648897745899740093467871 36973346618849610140201807)
        ·
          refine ⟨55460019928274415210302711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36973346618849610140201807 55460019928274415210302711)
          ·
            refine ⟨83190029892411622815454067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55460019928274415210302711 83190029892411622815454067)
            ·
              refine ⟨124785044838617434223181101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83190029892411622815454067 124785044838617434223181101)
              ·
                refine ⟨46794391814481537833692913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124785044838617434223181101 46794391814481537833692913)
                ·
                  refine ⟨35095793860861153375269685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46794391814481537833692913 35095793860861153375269685)
                  ·
                    refine ⟨3290230674455733128931533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35095793860861153375269685 3290230674455733128931533)
                    ·
                      refine ⟨1233836502920899923349325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290230674455733128931533 1233836502920899923349325)
                      ·
                        rfl

theorem cell23_2402888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2402888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402888 prefixEnd_2402888 := by exact prefixLift 2402888
  have htrace : WordTrace (prefixWord ++ tailWord_2402888) baseStart_2402888 baseEnd_2402888 := by
    simpa [prefixWord, tailWord_2402888, baseEnd_2402888] using wordTrace_append hprefix tailTrace_2402888
  have hstable : (prefixWord ++ tailWord_2402888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402888).length < 2 ^ (prefixWord ++ tailWord_2402888).sum := by decide
  have hdescent : baseEnd_2402888 < baseStart_2402888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402922 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2402922 : Nat := 118140960795 + 2402922 * 2 ^ 59
def prefixEnd_2402922 : Nat := 4983230072969 + 3 ^ 40 * 2402922 * 2
def baseEnd_2402922 : Nat := 1233853961263152790324169

theorem tailTrace_2402922 : CollatzResearch.WordTrace tailWord_2402922 prefixEnd_2402922 1233853961263152790324169 := by
  unfold tailWord_2402922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21910441350157863812544755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58427843600420970166786013 21910441350157863812544755)
  ·
    refine ⟨32865662025236795718817133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21910441350157863812544755 32865662025236795718817133)
    ·
      refine ⟨12324623259463798394556425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32865662025236795718817133 12324623259463798394556425)
      ·
        refine ⟨9243467444597848795917319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324623259463798394556425 9243467444597848795917319)
        ·
          refine ⟨13865201166896773193875979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243467444597848795917319 13865201166896773193875979)
          ·
            refine ⟨20797801750345159790813969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13865201166896773193875979 20797801750345159790813969)
            ·
              refine ⟨15598351312758869843110477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20797801750345159790813969 15598351312758869843110477)
              ·
                refine ⟨5849381742284576191166429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15598351312758869843110477 5849381742284576191166429)
                ·
                  refine ⟨2193518153356716071687411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5849381742284576191166429 2193518153356716071687411)
                  ·
                    refine ⟨3290277230035074107531117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2193518153356716071687411 3290277230035074107531117)
                    ·
                      refine ⟨1233853961263152790324169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290277230035074107531117 1233853961263152790324169)
                      ·
                        rfl

theorem cell23_2402922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2402922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402922 prefixEnd_2402922 := by exact prefixLift 2402922
  have htrace : WordTrace (prefixWord ++ tailWord_2402922) baseStart_2402922 baseEnd_2402922 := by
    simpa [prefixWord, tailWord_2402922, baseEnd_2402922] using wordTrace_append hprefix tailTrace_2402922
  have hstable : (prefixWord ++ tailWord_2402922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402922).length < 2 ^ (prefixWord ++ tailWord_2402922).sum := by decide
  have hdescent : baseEnd_2402922 < baseStart_2402922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402925 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2402925 : Nat := 118140960795 + 2402925 * 2 ^ 59
def prefixEnd_2402925 : Nat := 4983230072969 + 3 ^ 40 * 2402925 * 2
def baseEnd_2402925 : Nat := 411285167235038759528885

theorem tailTrace_2402925 : CollatzResearch.WordTrace tailWord_2402925 prefixEnd_2402925 411285167235038759528885 := by
  unfold tailWord_2402925
  simp only [CollatzResearch.WordTrace]
  refine ⟨87641874819620586762538229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58427916546413724508358819 87641874819620586762538229)
  ·
    refine ⟨8216425764339430008987959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87641874819620586762538229 8216425764339430008987959)
    ·
      refine ⟨12324638646509145013481939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216425764339430008987959 12324638646509145013481939)
      ·
        refine ⟨18486957969763717520222909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324638646509145013481939 18486957969763717520222909)
        ·
          refine ⟨6932609238661394070083591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18486957969763717520222909 6932609238661394070083591)
          ·
            refine ⟨10398913857992091105125387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6932609238661394070083591 10398913857992091105125387)
            ·
              refine ⟨15598370786988136657688081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398913857992091105125387 15598370786988136657688081)
              ·
                refine ⟨11698778090241102493266061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15598370786988136657688081 11698778090241102493266061)
                ·
                  refine ⟨4387041783840413434974773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11698778090241102493266061 4387041783840413434974773)
                  ·
                    refine ⟨411285167235038759528885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4387041783840413434974773 411285167235038759528885)
                    ·
                      rfl

theorem cell23_2402925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2402925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402925 prefixEnd_2402925 := by exact prefixLift 2402925
  have htrace : WordTrace (prefixWord ++ tailWord_2402925) baseStart_2402925 baseEnd_2402925 := by
    simpa [prefixWord, tailWord_2402925, baseEnd_2402925] using wordTrace_append hprefix tailTrace_2402925
  have hstable : (prefixWord ++ tailWord_2402925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402925).length < 2 ^ (prefixWord ++ tailWord_2402925).sum := by decide
  have hdescent : baseEnd_2402925 < baseStart_2402925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402945 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2402945 : Nat := 118140960795 + 2402945 * 2 ^ 59
def prefixEnd_2402945 : Nat := 4983230072969 + 3 ^ 40 * 2402945 * 2
def baseEnd_2402945 : Nat := 1233865771318206200336563

theorem tailTrace_2402945 : CollatzResearch.WordTrace tailWord_2402945 prefixEnd_2402945 1233865771318206200336563 := by
  unfold tailWord_2402945
  simp only [CollatzResearch.WordTrace]
  refine ⟨87642604279548130178266289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58428402853032086785510859 87642604279548130178266289)
  ·
    refine ⟨65731953209661097633699717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87642604279548130178266289 65731953209661097633699717)
    ·
      refine ⟨12324741226811455806318697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65731953209661097633699717 12324741226811455806318697)
      ·
        refine ⟨9243555920108591854739023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324741226811455806318697 9243555920108591854739023)
        ·
          refine ⟨13865333880162887782108535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243555920108591854739023 13865333880162887782108535)
          ·
            refine ⟨20798000820244331673162803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13865333880162887782108535 20798000820244331673162803)
            ·
              refine ⟨31197001230366497509744205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20798000820244331673162803 31197001230366497509744205)
              ·
                refine ⟨11698875461387436566154077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31197001230366497509744205 11698875461387436566154077)
                ·
                  refine ⟨4387078298020288712307779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11698875461387436566154077 4387078298020288712307779)
                  ·
                    refine ⟨6580617447030433068461669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387078298020288712307779 6580617447030433068461669)
                    ·
                      refine ⟨1233865771318206200336563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6580617447030433068461669 1233865771318206200336563)
                      ·
                        rfl

theorem cell23_2402945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2402945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402945 prefixEnd_2402945 := by exact prefixLift 2402945
  have htrace : WordTrace (prefixWord ++ tailWord_2402945) baseStart_2402945 baseEnd_2402945 := by
    simpa [prefixWord, tailWord_2402945, baseEnd_2402945] using wordTrace_append hprefix tailTrace_2402945
  have hstable : (prefixWord ++ tailWord_2402945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402945).length < 2 ^ (prefixWord ++ tailWord_2402945).sum := by decide
  have hdescent : baseEnd_2402945 < baseStart_2402945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402949 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_2402949 : Nat := 118140960795 + 2402949 * 2 ^ 59
def prefixEnd_2402949 : Nat := 4983230072969 + 3 ^ 40 * 2402949 * 2
def baseEnd_2402949 : Nat := 1233867825240824184686545

theorem tailTrace_2402949 : CollatzResearch.WordTrace tailWord_2402949 prefixEnd_2402949 1233867825240824184686545 := by
  unfold tailWord_2402949
  simp only [CollatzResearch.WordTrace]
  refine ⟨87642750171533638861411901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58428500114355759240941267 87642750171533638861411901)
  ·
    refine ⟨32866031314325114573029463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87642750171533638861411901 32866031314325114573029463)
    ·
      refine ⟨49299046971487671859544195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32866031314325114573029463 49299046971487671859544195)
      ·
        refine ⟨73948570457231507789316293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49299046971487671859544195 73948570457231507789316293)
        ·
          refine ⟨13865356960730907710496805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73948570457231507789316293 13865356960730907710496805)
          ·
            refine ⟨2599754430137045195718151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13865356960730907710496805 2599754430137045195718151)
            ·
              refine ⟨3899631645205567793577227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599754430137045195718151 3899631645205567793577227)
              ·
                refine ⟨5849447467808351690365841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899631645205567793577227 5849447467808351690365841)
                ·
                  refine ⟨4387085600856263767774381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849447467808351690365841 4387085600856263767774381)
                  ·
                    refine ⟨1645157100321098912915393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4387085600856263767774381 1645157100321098912915393)
                    ·
                      refine ⟨1233867825240824184686545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645157100321098912915393 1233867825240824184686545)
                      ·
                        rfl

theorem cell23_2402949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_2402949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402949 prefixEnd_2402949 := by exact prefixLift 2402949
  have htrace : WordTrace (prefixWord ++ tailWord_2402949) baseStart_2402949 baseEnd_2402949 := by
    simpa [prefixWord, tailWord_2402949, baseEnd_2402949] using wordTrace_append hprefix tailTrace_2402949
  have hstable : (prefixWord ++ tailWord_2402949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402949).length < 2 ^ (prefixWord ++ tailWord_2402949).sum := by decide
  have hdescent : baseEnd_2402949 < baseStart_2402949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402968 : List Nat := [2, 1, 2, 4, 1, 1, 12]
def baseStart_2402968 : Nat := 118140960795 + 2402968 * 2 ^ 59
def prefixEnd_2402968 : Nat := 4983230072969 + 3 ^ 40 * 2402968 * 2
def baseEnd_2402968 : Nat := 15233056560163698893197

theorem tailTrace_2402968 : CollatzResearch.WordTrace tailWord_2402968 prefixEnd_2402968 15233056560163698893197 := by
  unfold tailWord_2402968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43821721579232402553176779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58428962105643203404235705 43821721579232402553176779)
  ·
    refine ⟨65732582368848603829765169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43821721579232402553176779 65732582368848603829765169)
    ·
      refine ⟨49299436776636452872323877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65732582368848603829765169 49299436776636452872323877)
      ·
        refine ⟨9243644395619334913560727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49299436776636452872323877 9243644395619334913560727)
        ·
          refine ⟨13865466593429002370341091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243644395619334913560727 13865466593429002370341091)
          ·
            refine ⟨20798199890143503555511637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13865466593429002370341091 20798199890143503555511637)
            ·
              refine ⟨15233056560163698893197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20798199890143503555511637 15233056560163698893197)
              ·
                rfl

theorem cell23_2402968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 12].length) (baseStart_2402968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402968 prefixEnd_2402968 := by exact prefixLift 2402968
  have htrace : WordTrace (prefixWord ++ tailWord_2402968) baseStart_2402968 baseEnd_2402968 := by
    simpa [prefixWord, tailWord_2402968, baseEnd_2402968] using wordTrace_append hprefix tailTrace_2402968
  have hstable : (prefixWord ++ tailWord_2402968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402968).length < 2 ^ (prefixWord ++ tailWord_2402968).sum := by decide
  have hdescent : baseEnd_2402968 < baseStart_2402968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402972 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2402972 : Nat := 118140960795 + 2402972 * 2 ^ 59
def prefixEnd_2402972 : Nat := 4983230072969 + 3 ^ 40 * 2402972 * 2
def baseEnd_2402972 : Nat := 411293211765292531566313

theorem tailTrace_2402972 : CollatzResearch.WordTrace tailWord_2402972 prefixEnd_2402972 411293211765292531566313 := by
  unfold tailWord_2402972
  simp only [CollatzResearch.WordTrace]
  refine ⟨43821794525225156894749585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58429059366966875859666113 43821794525225156894749585)
  ·
    refine ⟨32866345893918867671062189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43821794525225156894749585 32866345893918867671062189)
    ·
      refine ⟨12324879710219575376648321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32866345893918867671062189 12324879710219575376648321)
      ·
        refine ⟨9243659782664681532486241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324879710219575376648321 9243659782664681532486241)
        ·
          refine ⟨6932744836998511149364681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9243659782664681532486241 6932744836998511149364681)
          ·
            refine ⟨5199558627748883362023511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6932744836998511149364681 5199558627748883362023511)
            ·
              refine ⟨7799337941623325043035267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199558627748883362023511 7799337941623325043035267)
              ·
                refine ⟨11699006912434987564552901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799337941623325043035267 11699006912434987564552901)
                ·
                  refine ⟨2193563796081560168353669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11699006912434987564552901 2193563796081560168353669)
                  ·
                    refine ⟨411293211765292531566313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193563796081560168353669 411293211765292531566313)
                    ·
                      rfl

theorem cell23_2402972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2402972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402972 prefixEnd_2402972 := by exact prefixLift 2402972
  have htrace : WordTrace (prefixWord ++ tailWord_2402972) baseStart_2402972 baseEnd_2402972 := by
    simpa [prefixWord, tailWord_2402972, baseEnd_2402972] using wordTrace_append hprefix tailTrace_2402972
  have hstable : (prefixWord ++ tailWord_2402972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402972).length < 2 ^ (prefixWord ++ tailWord_2402972).sum := by decide
  have hdescent : baseEnd_2402972 < baseStart_2402972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2402999 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_2402999 : Nat := 118140960795 + 2402999 * 2 ^ 59
def prefixEnd_2402999 : Nat := 4983230072969 + 3 ^ 40 * 2402999 * 2
def baseEnd_2402999 : Nat := 1233893499273548989061315

theorem tailTrace_2402999 : CollatzResearch.WordTrace tailWord_2402999 prefixEnd_2402999 1233893499273548989061315 := by
  unfold tailWord_2402999
  simp only [CollatzResearch.WordTrace]
  refine ⟨87644573821352497400732051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58429715880901664933821367 87644573821352497400732051)
  ·
    refine ⟨131466860732028746101098077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87644573821352497400732051 131466860732028746101098077)
    ·
      refine ⟨49300072774510779787911779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131466860732028746101098077 49300072774510779787911779)
      ·
        refine ⟨73950109161766169681867669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49300072774510779787911779 73950109161766169681867669)
        ·
          refine ⟨3466411366957789203837547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73950109161766169681867669 3466411366957789203837547)
          ·
            refine ⟨5199617050436683805756321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466411366957789203837547 5199617050436683805756321)
            ·
              refine ⟨3899712787827512854317241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5199617050436683805756321 3899712787827512854317241)
              ·
                refine ⟨2924784590870634640737931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899712787827512854317241 2924784590870634640737931)
                ·
                  refine ⟨4387176886305951961106897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924784590870634640737931 4387176886305951961106897)
                  ·
                    refine ⟨3290382664729463970830173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4387176886305951961106897 3290382664729463970830173)
                    ·
                      refine ⟨1233893499273548989061315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290382664729463970830173 1233893499273548989061315)
                      ·
                        rfl

theorem cell23_2402999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_2402999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2402999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2402999 prefixEnd_2402999 := by exact prefixLift 2402999
  have htrace : WordTrace (prefixWord ++ tailWord_2402999) baseStart_2402999 baseEnd_2402999 := by
    simpa [prefixWord, tailWord_2402999, baseEnd_2402999] using wordTrace_append hprefix tailTrace_2402999
  have hstable : (prefixWord ++ tailWord_2402999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2402999).length < 2 ^ (prefixWord ++ tailWord_2402999).sum := by decide
  have hdescent : baseEnd_2402999 < baseStart_2402999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2402999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403052 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_2403052 : Nat := 118140960795 + 2403052 * 2 ^ 59
def prefixEnd_2403052 : Nat := 4983230072969 + 3 ^ 40 * 2403052 * 2
def baseEnd_2403052 : Nat := 1233920713748237281698571

theorem tailTrace_2403052 : CollatzResearch.WordTrace tailWord_2403052 prefixEnd_2403052 1233920713748237281698571 := by
  unfold tailWord_2403052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43823253445080243726205705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58431004593440324968274273 43823253445080243726205705)
  ·
    refine ⟨32867440083810182794654279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43823253445080243726205705 32867440083810182794654279)
    ·
      refine ⟨49301160125715274191981419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32867440083810182794654279 49301160125715274191981419)
      ·
        refine ⟨73951740188572911287972129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49301160125715274191981419 73951740188572911287972129)
        ·
          refine ⟨55463805141429683465979097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73951740188572911287972129 55463805141429683465979097)
          ·
            refine ⟨41597853856072262599484323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55463805141429683465979097 41597853856072262599484323)
            ·
              refine ⟨62396780784108393899226485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41597853856072262599484323 62396780784108393899226485)
              ·
                refine ⟨5849698198510161928052483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62396780784108393899226485 5849698198510161928052483)
                ·
                  refine ⟨8774547297765242892078725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5849698198510161928052483 8774547297765242892078725)
                  ·
                    refine ⟨1645227618330983042264761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8774547297765242892078725 1645227618330983042264761)
                    ·
                      refine ⟨1233920713748237281698571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645227618330983042264761 1233920713748237281698571)
                      ·
                        rfl

theorem cell23_2403052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_2403052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403052 prefixEnd_2403052 := by exact prefixLift 2403052
  have htrace : WordTrace (prefixWord ++ tailWord_2403052) baseStart_2403052 baseEnd_2403052 := by
    simpa [prefixWord, tailWord_2403052, baseEnd_2403052] using wordTrace_append hprefix tailTrace_2403052
  have hstable : (prefixWord ++ tailWord_2403052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403052).length < 2 ^ (prefixWord ++ tailWord_2403052).sum := by decide
  have hdescent : baseEnd_2403052 < baseStart_2403052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403055 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_2403055 : Nat := 118140960795 + 2403055 * 2 ^ 59
def prefixEnd_2403055 : Nat := 4983230072969 + 3 ^ 40 * 2403055 * 2
def baseEnd_2403055 : Nat := 1233922254190200769961057

theorem tailTrace_2403055 : CollatzResearch.WordTrace tailWord_2403055 prefixEnd_2403055 1233922254190200769961057 := by
  unfold tailWord_2403055
  simp only [CollatzResearch.WordTrace]
  refine ⟨87646616309149618964770619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58431077539433079309847079 87646616309149618964770619)
  ·
    refine ⟨131469924463724428447155929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87646616309149618964770619 131469924463724428447155929)
    ·
      refine ⟨98602443347793321335366947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131469924463724428447155929 98602443347793321335366947)
      ·
        refine ⟨147903665021689982003050421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98602443347793321335366947 147903665021689982003050421)
        ·
          refine ⟨13865968595783435812785977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147903665021689982003050421 13865968595783435812785977)
          ·
            refine ⟨10399476446837576859589483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13865968595783435812785977 10399476446837576859589483)
            ·
              refine ⟨15599214670256365289384225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10399476446837576859589483 15599214670256365289384225)
              ·
                refine ⟨11699411002692273967038169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15599214670256365289384225 11699411002692273967038169)
                ·
                  refine ⟨8774558252019205475278627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11699411002692273967038169 8774558252019205475278627)
                  ·
                    refine ⟨13161837378028808212917941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8774558252019205475278627 13161837378028808212917941)
                    ·
                      refine ⟨1233922254190200769961057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13161837378028808212917941 1233922254190200769961057)
                      ·
                        rfl

theorem cell23_2403055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_2403055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403055 prefixEnd_2403055 := by exact prefixLift 2403055
  have htrace : WordTrace (prefixWord ++ tailWord_2403055) baseStart_2403055 baseEnd_2403055 := by
    simpa [prefixWord, tailWord_2403055, baseEnd_2403055] using wordTrace_append hprefix tailTrace_2403055
  have hstable : (prefixWord ++ tailWord_2403055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403055).length < 2 ^ (prefixWord ++ tailWord_2403055).sum := by decide
  have hdescent : baseEnd_2403055 < baseStart_2403055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403105 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2403105 : Nat := 118140960795 + 2403105 * 2 ^ 59
def prefixEnd_2403105 : Nat := 4983230072969 + 3 ^ 40 * 2403105 * 2
def baseEnd_2403105 : Nat := 411315976074308524778609

theorem tailTrace_2403105 : CollatzResearch.WordTrace tailWord_2403105 prefixEnd_2403105 411315976074308524778609 := by
  unfold tailWord_2403105
  simp only [CollatzResearch.WordTrace]
  refine ⟨87648439958968477504090769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58432293305978985002727179 87648439958968477504090769)
  ·
    refine ⟨65736329969226358128068077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87648439958968477504090769 65736329969226358128068077)
    ·
      refine ⟨24651123738459884298025529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65736329969226358128068077 24651123738459884298025529)
      ·
        refine ⟨18488342803844913223519147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24651123738459884298025529 18488342803844913223519147)
        ·
          refine ⟨27732514205767369835278721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18488342803844913223519147 27732514205767369835278721)
          ·
            refine ⟨20799385654325527376459041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27732514205767369835278721 20799385654325527376459041)
            ·
              refine ⟨15599539240744145532344281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20799385654325527376459041 15599539240744145532344281)
              ·
                refine ⟨11699654430558109149258211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15599539240744145532344281 11699654430558109149258211)
                ·
                  refine ⟨17549481645837163723887317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11699654430558109149258211 17549481645837163723887317)
                  ·
                    refine ⟨411315976074308524778609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17549481645837163723887317 411315976074308524778609)
                    ·
                      rfl

theorem cell23_2403105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2403105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403105 prefixEnd_2403105 := by exact prefixLift 2403105
  have htrace : WordTrace (prefixWord ++ tailWord_2403105) baseStart_2403105 baseEnd_2403105 := by
    simpa [prefixWord, tailWord_2403105, baseEnd_2403105] using wordTrace_append hprefix tailTrace_2403105
  have hstable : (prefixWord ++ tailWord_2403105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403105).length < 2 ^ (prefixWord ++ tailWord_2403105).sum := by decide
  have hdescent : baseEnd_2403105 < baseStart_2403105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403137 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2403137 : Nat := 118140960795 + 2403137 * 2 ^ 59
def prefixEnd_2403137 : Nat := 4983230072969 + 3 ^ 40 * 2403137 * 2
def baseEnd_2403137 : Nat := 1233964359603869449135681

theorem tailTrace_2403137 : CollatzResearch.WordTrace tailWord_2403137 prefixEnd_2403137 1233964359603869449135681 := by
  unfold tailWord_2403137
  simp only [CollatzResearch.WordTrace]
  refine ⟨87649607094852546969255665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58433071396568364646170443 87649607094852546969255665)
  ·
    refine ⟨65737205321139410226941749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87649607094852546969255665 65737205321139410226941749)
    ·
      refine ⟨6162862998856819708775789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65737205321139410226941749 6162862998856819708775789)
      ·
        refine ⟨2311073624571307390790921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6162862998856819708775789 2311073624571307390790921)
        ·
          refine ⟨1733305218428480543093191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2311073624571307390790921 1733305218428480543093191)
          ·
            refine ⟨2599957827642720814639787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733305218428480543093191 2599957827642720814639787)
            ·
              refine ⟨3899936741464081221959681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599957827642720814639787 3899936741464081221959681)
              ·
                refine ⟨2924952556098060916469761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899936741464081221959681 2924952556098060916469761)
                ·
                  refine ⟨2193714417073545687352321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2924952556098060916469761 2193714417073545687352321)
                  ·
                    refine ⟨1645285812805159265514241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2193714417073545687352321 1645285812805159265514241)
                    ·
                      refine ⟨1233964359603869449135681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645285812805159265514241 1233964359603869449135681)
                      ·
                        rfl

theorem cell23_2403137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2403137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403137 prefixEnd_2403137 := by exact prefixLift 2403137
  have htrace : WordTrace (prefixWord ++ tailWord_2403137) baseStart_2403137 baseEnd_2403137 := by
    simpa [prefixWord, tailWord_2403137, baseEnd_2403137] using wordTrace_append hprefix tailTrace_2403137
  have hstable : (prefixWord ++ tailWord_2403137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403137).length < 2 ^ (prefixWord ++ tailWord_2403137).sum := by decide
  have hdescent : baseEnd_2403137 < baseStart_2403137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403152 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_2403152 : Nat := 118140960795 + 2403152 * 2 ^ 59
def prefixEnd_2403152 : Nat := 4983230072969 + 3 ^ 40 * 2403152 * 2
def baseEnd_2403152 : Nat := 411324020604562296816037

theorem tailTrace_2403152 : CollatzResearch.WordTrace tailWord_2403152 prefixEnd_2403152 411324020604562296816037 := by
  unfold tailWord_2403152
  simp only [CollatzResearch.WordTrace]
  refine ⟨43825077094899102265525855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58433436126532136354034473 43825077094899102265525855)
  ·
    refine ⟨65737615642348653398288783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43825077094899102265525855 65737615642348653398288783)
    ·
      refine ⟨98606423463522980097433175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65737615642348653398288783 98606423463522980097433175)
      ·
        refine ⟨147909635195284470146149763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98606423463522980097433175 147909635195284470146149763)
        ·
          refine ⟨221864452792926705219224645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147909635195284470146149763 221864452792926705219224645)
          ·
            refine ⟨41599584898673757228604621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221864452792926705219224645 41599584898673757228604621)
            ·
              refine ⟨15599844337002658960726733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41599584898673757228604621 15599844337002658960726733)
              ·
                refine ⟨5849941626375997110272525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15599844337002658960726733 5849941626375997110272525)
                ·
                  refine ⟨2193728109890998916352197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5849941626375997110272525 2193728109890998916352197)
                  ·
                    refine ⟨411324020604562296816037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193728109890998916352197 411324020604562296816037)
                    ·
                      rfl

theorem cell23_2403152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_2403152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403152 prefixEnd_2403152 := by exact prefixLift 2403152
  have htrace : WordTrace (prefixWord ++ tailWord_2403152) baseStart_2403152 baseEnd_2403152 := by
    simpa [prefixWord, tailWord_2403152, baseEnd_2403152] using wordTrace_append hprefix tailTrace_2403152
  have hstable : (prefixWord ++ tailWord_2403152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403152).length < 2 ^ (prefixWord ++ tailWord_2403152).sum := by decide
  have hdescent : baseEnd_2403152 < baseStart_2403152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403159 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_2403159 : Nat := 118140960795 + 2403159 * 2 ^ 59
def prefixEnd_2403159 : Nat := 4983230072969 + 3 ^ 40 * 2403159 * 2
def baseEnd_2403159 : Nat := 1233975656178268363060579

theorem tailTrace_2403159 : CollatzResearch.WordTrace tailWord_2403159 prefixEnd_2403159 1233975656178268363060579 := by
  unfold tailWord_2403159
  simp only [CollatzResearch.WordTrace]
  refine ⟨87650409500772844726556531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58433606333848563151037687 87650409500772844726556531)
  ·
    refine ⟨131475614251159267089834797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87650409500772844726556531 131475614251159267089834797)
    ·
      refine ⟨49303355344184725158688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131475614251159267089834797 49303355344184725158688049)
      ·
        refine ⟨36977516508138543869016037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49303355344184725158688049 36977516508138543869016037)
        ·
          refine ⟨6933284345275976975440507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36977516508138543869016037 6933284345275976975440507)
          ·
            refine ⟨10399926517913965463160761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6933284345275976975440507 10399926517913965463160761)
            ·
              refine ⟨7799944888435474097370571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10399926517913965463160761 7799944888435474097370571)
              ·
                refine ⟨11699917332653211146055857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799944888435474097370571 11699917332653211146055857)
                ·
                  refine ⟨8774937999489908359541893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11699917332653211146055857 8774937999489908359541893)
                  ·
                    refine ⟨1645300874904357817414105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8774937999489908359541893 1645300874904357817414105)
                    ·
                      refine ⟨1233975656178268363060579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645300874904357817414105 1233975656178268363060579)
                      ·
                        rfl

theorem cell23_2403159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_2403159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403159 prefixEnd_2403159 := by exact prefixLift 2403159
  have htrace : WordTrace (prefixWord ++ tailWord_2403159) baseStart_2403159 baseEnd_2403159 := by
    simpa [prefixWord, tailWord_2403159, baseEnd_2403159] using wordTrace_append hprefix tailTrace_2403159
  have hstable : (prefixWord ++ tailWord_2403159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403159).length < 2 ^ (prefixWord ++ tailWord_2403159).sum := by decide
  have hdescent : baseEnd_2403159 < baseStart_2403159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403162 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2403162 : Nat := 118140960795 + 2403162 * 2 ^ 59
def prefixEnd_2403162 : Nat := 4983230072969 + 3 ^ 40 * 2403162 * 2
def baseEnd_2403162 : Nat := 1233977196620231851323065

theorem tailTrace_2403162 : CollatzResearch.WordTrace tailWord_2403162 prefixEnd_2403162 1233977196620231851323065 := by
  unfold tailWord_2403162
  simp only [CollatzResearch.WordTrace]
  refine ⟨21912629729940494059728935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58433679279841317492610493 21912629729940494059728935)
  ·
    refine ⟨32868944594910741089593403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21912629729940494059728935 32868944594910741089593403)
    ·
      refine ⟨49303416892366111634390105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32868944594910741089593403 49303416892366111634390105)
      ·
        refine ⟨36977562669274583725792579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49303416892366111634390105 36977562669274583725792579)
        ·
          refine ⟨55466344003911875588688869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36977562669274583725792579 55466344003911875588688869)
          ·
            refine ⟨10399939500733476672879163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55466344003911875588688869 10399939500733476672879163)
            ·
              refine ⟨15599909251100215009318745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10399939500733476672879163 15599909251100215009318745)
              ·
                refine ⟨11699931938325161256989059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15599909251100215009318745 11699931938325161256989059)
                ·
                  refine ⟨17549897907487741885483589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11699931938325161256989059 17549897907487741885483589)
                  ·
                    refine ⟨3290605857653951603528173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17549897907487741885483589 3290605857653951603528173)
                    ·
                      refine ⟨1233977196620231851323065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290605857653951603528173 1233977196620231851323065)
                      ·
                        rfl

theorem cell23_2403162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2403162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403162 prefixEnd_2403162 := by exact prefixLift 2403162
  have htrace : WordTrace (prefixWord ++ tailWord_2403162) baseStart_2403162 baseEnd_2403162 := by
    simpa [prefixWord, tailWord_2403162, baseEnd_2403162] using wordTrace_append hprefix tailTrace_2403162
  have hstable : (prefixWord ++ tailWord_2403162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403162).length < 2 ^ (prefixWord ++ tailWord_2403162).sum := by decide
  have hdescent : baseEnd_2403162 < baseStart_2403162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403186 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_2403186 : Nat := 118140960795 + 2403186 * 2 ^ 59
def prefixEnd_2403186 : Nat := 4983230072969 + 3 ^ 40 * 2403186 * 2
def baseEnd_2403186 : Nat := 411329840051979919140985

theorem tailTrace_2403186 : CollatzResearch.WordTrace tailWord_2403186 prefixEnd_2403186 411329840051979919140985 := by
  unfold tailWord_2403186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21912848567918757084447353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58434262847783352225192941 21912848567918757084447353)
  ·
    refine ⟨16434636425939067813335515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21912848567918757084447353 16434636425939067813335515)
    ·
      refine ⟨24651954638908601720003273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16434636425939067813335515 24651954638908601720003273)
      ·
        refine ⟨18488965979181451290002455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24651954638908601720003273 18488965979181451290002455)
        ·
          refine ⟨27733448968772176935003683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18488965979181451290002455 27733448968772176935003683)
          ·
            refine ⟨41600173453158265402505525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27733448968772176935003683 41600173453158265402505525)
            ·
              refine ⟨3900016261233587381484893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41600173453158265402505525 3900016261233587381484893)
              ·
                refine ⟨1462506097962595268056835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3900016261233587381484893 1462506097962595268056835)
                ·
                  refine ⟨2193759146943892902085253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462506097962595268056835 2193759146943892902085253)
                  ·
                    refine ⟨411329840051979919140985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193759146943892902085253 411329840051979919140985)
                    ·
                      rfl

theorem cell23_2403186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_2403186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403186 prefixEnd_2403186 := by exact prefixLift 2403186
  have htrace : WordTrace (prefixWord ++ tailWord_2403186) baseStart_2403186 baseEnd_2403186 := by
    simpa [prefixWord, tailWord_2403186, baseEnd_2403186] using wordTrace_append hprefix tailTrace_2403186
  have hstable : (prefixWord ++ tailWord_2403186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403186).length < 2 ^ (prefixWord ++ tailWord_2403186).sum := by decide
  have hdescent : baseEnd_2403186 < baseStart_2403186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403236 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_2403236 : Nat := 118140960795 + 2403236 * 2 ^ 59
def prefixEnd_2403236 : Nat := 4983230072969 + 3 ^ 40 * 2403236 * 2
def baseEnd_2403236 : Nat := 1234015194188664561797725

theorem tailTrace_2403236 : CollatzResearch.WordTrace tailWord_2403236 prefixEnd_2403236 1234015194188664561797725 := by
  unfold tailWord_2403236
  simp only [CollatzResearch.WordTrace]
  refine ⟨43826608960746943438554781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58435478614329257918073041 43826608960746943438554781)
  ·
    refine ⟨16434978360280103789458043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43826608960746943438554781 16434978360280103789458043)
    ·
      refine ⟨24652467540420155684187065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16434978360280103789458043 24652467540420155684187065)
      ·
        refine ⟨18489350655315116763140299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24652467540420155684187065 18489350655315116763140299)
        ·
          refine ⟨27734025982972675144710449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18489350655315116763140299 27734025982972675144710449)
          ·
            refine ⟨20800519487229506358532837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27734025982972675144710449 20800519487229506358532837)
            ·
              refine ⟨3900097403855532442224907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20800519487229506358532837 3900097403855532442224907)
              ·
                refine ⟨5850146105783298663337361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900097403855532442224907 5850146105783298663337361)
                ·
                  refine ⟨4387609579337473997503021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850146105783298663337361 4387609579337473997503021)
                  ·
                    refine ⟨1645353592251552749063633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4387609579337473997503021 1645353592251552749063633)
                    ·
                      refine ⟨1234015194188664561797725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645353592251552749063633 1234015194188664561797725)
                      ·
                        rfl

theorem cell23_2403236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_2403236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403236 prefixEnd_2403236 := by exact prefixLift 2403236
  have htrace : WordTrace (prefixWord ++ tailWord_2403236) baseStart_2403236 baseEnd_2403236 := by
    simpa [prefixWord, tailWord_2403236, baseEnd_2403236] using wordTrace_append hprefix tailTrace_2403236
  have hstable : (prefixWord ++ tailWord_2403236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403236).length < 2 ^ (prefixWord ++ tailWord_2403236).sum := by decide
  have hdescent : baseEnd_2403236 < baseStart_2403236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403277 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2403277 : Nat := 118140960795 + 2403277 * 2 ^ 59
def prefixEnd_2403277 : Nat := 4983230072969 + 3 ^ 40 * 2403277 * 2
def baseEnd_2403277 : Nat := 1234036246895498901385037

theorem tailTrace_2403277 : CollatzResearch.WordTrace tailWord_2403277 prefixEnd_2403277 1234036246895498901385037 := by
  unfold tailWord_2403277
  simp only [CollatzResearch.WordTrace]
  refine ⟨87654713314345350879352085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58436475542896900586234723 87654713314345350879352085)
  ·
    refine ⟨4108814686609938322469629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87654713314345350879352085 4108814686609938322469629)
    ·
      refine ⟨1540805507478726870926111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4108814686609938322469629 1540805507478726870926111)
      ·
        refine ⟨2311208261218090306389167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540805507478726870926111 2311208261218090306389167)
        ·
          refine ⟨3466812391827135459583751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311208261218090306389167 3466812391827135459583751)
          ·
            refine ⟨5200218587740703189375627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466812391827135459583751 5200218587740703189375627)
            ·
              refine ⟨7800327881611054784063441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200218587740703189375627 7800327881611054784063441)
              ·
                refine ⟨5850245911208291088047581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7800327881611054784063441 5850245911208291088047581)
                ·
                  refine ⟨2193842216703109158017843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5850245911208291088047581 2193842216703109158017843)
                  ·
                    refine ⟨3290763325054663737026765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2193842216703109158017843 3290763325054663737026765)
                    ·
                      refine ⟨1234036246895498901385037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290763325054663737026765 1234036246895498901385037)
                      ·
                        rfl

theorem cell23_2403277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2403277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403277 prefixEnd_2403277 := by exact prefixLift 2403277
  have htrace : WordTrace (prefixWord ++ tailWord_2403277) baseStart_2403277 baseEnd_2403277 := by
    simpa [prefixWord, tailWord_2403277, baseEnd_2403277] using wordTrace_append hprefix tailTrace_2403277
  have hstable : (prefixWord ++ tailWord_2403277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403277).length < 2 ^ (prefixWord ++ tailWord_2403277).sum := by decide
  have hdescent : baseEnd_2403277 < baseStart_2403277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403279 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_2403279 : Nat := 118140960795 + 2403279 * 2 ^ 59
def prefixEnd_2403279 : Nat := 4983230072969 + 3 ^ 40 * 2403279 * 2
def baseEnd_2403279 : Nat := 1234037273856807893560027

theorem tailTrace_2403279 : CollatzResearch.WordTrace tailWord_2403279 prefixEnd_2403279 1234037273856807893560027 := by
  unfold tailWord_2403279
  simp only [CollatzResearch.WordTrace]
  refine ⟨87654786260338105220924891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58436524173558736813949927 87654786260338105220924891)
  ·
    refine ⟨131482179390507157831387337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87654786260338105220924891 131482179390507157831387337)
    ·
      refine ⟨98611634542880368373540503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131482179390507157831387337 98611634542880368373540503)
      ·
        refine ⟨147917451814320552560310755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98611634542880368373540503 147917451814320552560310755)
        ·
          refine ⟨221876177721480828840466133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147917451814320552560310755 221876177721480828840466133)
          ·
            refine ⟨5200222915347206925948425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 221876177721480828840466133 5200222915347206925948425)
            ·
              refine ⟨3900167186510405194461319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5200222915347206925948425 3900167186510405194461319)
              ·
                refine ⟨5850250779765607791691979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900167186510405194461319 5850250779765607791691979)
                ·
                  refine ⟨8775376169648411687537969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850250779765607791691979 8775376169648411687537969)
                  ·
                    refine ⟨6581532127236308765653477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8775376169648411687537969 6581532127236308765653477)
                    ·
                      refine ⟨1234037273856807893560027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6581532127236308765653477 1234037273856807893560027)
                      ·
                        rfl

theorem cell23_2403279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_2403279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403279 prefixEnd_2403279 := by exact prefixLift 2403279
  have htrace : WordTrace (prefixWord ++ tailWord_2403279) baseStart_2403279 baseEnd_2403279 := by
    simpa [prefixWord, tailWord_2403279, baseEnd_2403279] using wordTrace_append hprefix tailTrace_2403279
  have hstable : (prefixWord ++ tailWord_2403279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403279).length < 2 ^ (prefixWord ++ tailWord_2403279).sum := by decide
  have hdescent : baseEnd_2403279 < baseStart_2403279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403289 : List Nat := [1, 2, 1, 2, 5, 2, 3, 7]
def baseStart_2403289 : Nat := 118140960795 + 2403289 * 2 ^ 59
def prefixEnd_2403289 : Nat := 4983230072969 + 3 ^ 40 * 2403289 * 2
def baseEnd_2403289 : Nat := 45705274394938994608703

theorem tailTrace_2403289 : CollatzResearch.WordTrace tailWord_2403289 prefixEnd_2403289 45705274394938994608703 := by
  unfold tailWord_2403289
  simp only [CollatzResearch.WordTrace]
  refine ⟨87655150990301876928788921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58436767326867917952525947 87655150990301876928788921)
  ·
    refine ⟨65741363242726407696591691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87655150990301876928788921 65741363242726407696591691)
    ·
      refine ⟨98612044864089611544887537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65741363242726407696591691 98612044864089611544887537)
      ·
        refine ⟨73959033648067208658665653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98612044864089611544887537 73959033648067208658665653)
        ·
          refine ⟨6933659404506300811749905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73959033648067208658665653 6933659404506300811749905)
          ·
            refine ⟨5200244553379725608812429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6933659404506300811749905 5200244553379725608812429)
            ·
              refine ⟨1950091707517397103304661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5200244553379725608812429 1950091707517397103304661)
              ·
                refine ⟨45705274394938994608703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1950091707517397103304661 45705274394938994608703)
                ·
                  rfl

theorem cell23_2403289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 7].length) (baseStart_2403289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403289 prefixEnd_2403289 := by exact prefixLift 2403289
  have htrace : WordTrace (prefixWord ++ tailWord_2403289) baseStart_2403289 baseEnd_2403289 := by
    simpa [prefixWord, tailWord_2403289, baseEnd_2403289] using wordTrace_append hprefix tailTrace_2403289
  have hstable : (prefixWord ++ tailWord_2403289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403289).length < 2 ^ (prefixWord ++ tailWord_2403289).sum := by decide
  have hdescent : baseEnd_2403289 < baseStart_2403289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403299 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2403299 : Nat := 118140960795 + 2403299 * 2 ^ 59
def prefixEnd_2403299 : Nat := 4983230072969 + 3 ^ 40 * 2403299 * 2
def baseEnd_2403299 : Nat := 1234047543469897815309935

theorem tailTrace_2403299 : CollatzResearch.WordTrace tailWord_2403299 prefixEnd_2403299 1234047543469897815309935 := by
  unfold tailWord_2403299
  simp only [CollatzResearch.WordTrace]
  refine ⟨87655515720265648636652951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58437010480177099091101967 87655515720265648636652951)
  ·
    refine ⟨131483273580398472954979427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87655515720265648636652951 131483273580398472954979427)
    ·
      refine ⟨197224910370597709432469141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131483273580398472954979427 197224910370597709432469141)
      ·
        refine ⟨9244917673621767629646991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197224910370597709432469141 9244917673621767629646991)
        ·
          refine ⟨13867376510432651444470487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9244917673621767629646991 13867376510432651444470487)
          ·
            refine ⟨20801064765648977166705731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13867376510432651444470487 20801064765648977166705731)
            ·
              refine ⟨31201597148473465750058597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20801064765648977166705731 31201597148473465750058597)
              ·
                refine ⟨5850299465338774828135987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31201597148473465750058597 5850299465338774828135987)
                ·
                  refine ⟨8775449198008162242203981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850299465338774828135987 8775449198008162242203981)
                  ·
                    refine ⟨3290793449253060840826493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8775449198008162242203981 3290793449253060840826493)
                    ·
                      refine ⟨1234047543469897815309935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290793449253060840826493 1234047543469897815309935)
                      ·
                        rfl

theorem cell23_2403299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2403299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403299 prefixEnd_2403299 := by exact prefixLift 2403299
  have htrace : WordTrace (prefixWord ++ tailWord_2403299) baseStart_2403299 baseEnd_2403299 := by
    simpa [prefixWord, tailWord_2403299, baseEnd_2403299] using wordTrace_append hprefix tailTrace_2403299
  have hstable : (prefixWord ++ tailWord_2403299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403299).length < 2 ^ (prefixWord ++ tailWord_2403299).sum := by decide
  have hdescent : baseEnd_2403299 < baseStart_2403299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403303 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2403303 : Nat := 118140960795 + 2403303 * 2 ^ 59
def prefixEnd_2403303 : Nat := 4983230072969 + 3 ^ 40 * 2403303 * 2
def baseEnd_2403303 : Nat := 1234049597392515799659917

theorem tailTrace_2403303 : CollatzResearch.WordTrace tailWord_2403303 prefixEnd_2403303 1234049597392515799659917 := by
  unfold tailWord_2403303
  simp only [CollatzResearch.WordTrace]
  refine ⟨87655661612251157319798563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58437107741500771546532375 87655661612251157319798563)
  ·
    refine ⟨131483492418376735979697845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87655661612251157319798563 131483492418376735979697845)
    ·
      refine ⟨12326577414222818998096673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131483492418376735979697845 12326577414222818998096673)
      ·
        refine ⟨9244933060667114248572505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12326577414222818998096673 9244933060667114248572505)
        ·
          refine ⟨6933699795500335686429379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9244933060667114248572505 6933699795500335686429379)
          ·
            refine ⟨10400549693250503529644069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6933699795500335686429379 10400549693250503529644069)
            ·
              refine ⟨1950103067484469411808263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10400549693250503529644069 1950103067484469411808263)
              ·
                refine ⟨2925154601226704117712395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950103067484469411808263 2925154601226704117712395)
                ·
                  refine ⟨4387731901840056176568593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925154601226704117712395 4387731901840056176568593)
                  ·
                    refine ⟨3290798926380042132426445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4387731901840056176568593 3290798926380042132426445)
                    ·
                      refine ⟨1234049597392515799659917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290798926380042132426445 1234049597392515799659917)
                      ·
                        rfl

theorem cell23_2403303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2403303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403303 prefixEnd_2403303 := by exact prefixLift 2403303
  have htrace : WordTrace (prefixWord ++ tailWord_2403303) baseStart_2403303 baseEnd_2403303 := by
    simpa [prefixWord, tailWord_2403303, baseEnd_2403303] using wordTrace_append hprefix tailTrace_2403303
  have hstable : (prefixWord ++ tailWord_2403303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403303).length < 2 ^ (prefixWord ++ tailWord_2403303).sum := by decide
  have hdescent : baseEnd_2403303 < baseStart_2403303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403310 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2403310 : Nat := 118140960795 + 2403310 * 2 ^ 59
def prefixEnd_2403310 : Nat := 4983230072969 + 3 ^ 40 * 2403310 * 2
def baseEnd_2403310 : Nat := 411351063919032424090795

theorem tailTrace_2403310 : CollatzResearch.WordTrace tailWord_2403310 prefixEnd_2403310 411351063919032424090795 := by
  unfold tailWord_2403310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956989615403224689412923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58437277948817198343535589 10956989615403224689412923)
  ·
    refine ⟨16435484423104837034119385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10956989615403224689412923 16435484423104837034119385)
    ·
      refine ⟨12326613317328627775589539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16435484423104837034119385 12326613317328627775589539)
      ·
        refine ⟨18489919975992941663384309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12326613317328627775589539 18489919975992941663384309)
        ·
          refine ⟨1733429997749338280942279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18489919975992941663384309 1733429997749338280942279)
          ·
            refine ⟨2600144996624007421413419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733429997749338280942279 2600144996624007421413419)
            ·
              refine ⟨3900217494936011132120129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600144996624007421413419 3900217494936011132120129)
              ·
                refine ⟨2925163121202008349090097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900217494936011132120129 2925163121202008349090097)
                ·
                  refine ⟨2193872340901506261817573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925163121202008349090097 2193872340901506261817573)
                  ·
                    refine ⟨411351063919032424090795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193872340901506261817573 411351063919032424090795)
                    ·
                      rfl

theorem cell23_2403310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2403310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403310 prefixEnd_2403310 := by exact prefixLift 2403310
  have htrace : WordTrace (prefixWord ++ tailWord_2403310) baseStart_2403310 baseEnd_2403310 := by
    simpa [prefixWord, tailWord_2403310, baseEnd_2403310] using wordTrace_append hprefix tailTrace_2403310
  have hstable : (prefixWord ++ tailWord_2403310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403310).length < 2 ^ (prefixWord ++ tailWord_2403310).sum := by decide
  have hdescent : baseEnd_2403310 < baseStart_2403310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403317 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2403317 : Nat := 118140960795 + 2403317 * 2 ^ 59
def prefixEnd_2403317 : Nat := 4983230072969 + 3 ^ 40 * 2403317 * 2
def baseEnd_2403317 : Nat := 1234056786121678744884853

theorem tailTrace_2403317 : CollatzResearch.WordTrace tailWord_2403317 prefixEnd_2403317 1234056786121678744884853 := by
  unfold tailWord_2403317
  simp only [CollatzResearch.WordTrace]
  refine ⟨87656172234200437710808205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58437448156133625140538803 87656172234200437710808205)
  ·
    refine ⟨32871064587825164141553077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87656172234200437710808205 32871064587825164141553077)
    ·
      refine ⟨3081662305108609138270601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32871064587825164141553077 3081662305108609138270601)
      ·
        refine ⟨2311246728831456853702951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3081662305108609138270601 2311246728831456853702951)
        ·
          refine ⟨3466870093247185280554427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311246728831456853702951 3466870093247185280554427)
          ·
            refine ⟨5200305139870777920831641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466870093247185280554427 5200305139870777920831641)
            ·
              refine ⟨3900228854903083440623731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5200305139870777920831641 3900228854903083440623731)
              ·
                refine ⟨5850343282354625160935597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900228854903083440623731 5850343282354625160935597)
                ·
                  refine ⟨2193878730882984435350849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5850343282354625160935597 2193878730882984435350849)
                  ·
                    refine ⟨1645409048162238326513137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2193878730882984435350849 1645409048162238326513137)
                    ·
                      refine ⟨1234056786121678744884853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645409048162238326513137 1234056786121678744884853)
                      ·
                        rfl

theorem cell23_2403317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2403317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403317 prefixEnd_2403317 := by exact prefixLift 2403317
  have htrace : WordTrace (prefixWord ++ tailWord_2403317) baseStart_2403317 baseEnd_2403317 := by
    simpa [prefixWord, tailWord_2403317, baseEnd_2403317] using wordTrace_append hprefix tailTrace_2403317
  have hstable : (prefixWord ++ tailWord_2403317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403317).length < 2 ^ (prefixWord ++ tailWord_2403317).sum := by decide
  have hdescent : baseEnd_2403317 < baseStart_2403317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403322 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_2403322 : Nat := 118140960795 + 2403322 * 2 ^ 59
def prefixEnd_2403322 : Nat := 4983230072969 + 3 ^ 40 * 2403322 * 2
def baseEnd_2403322 : Nat := 1234059353524951225322329

theorem tailTrace_2403322 : CollatzResearch.WordTrace tailWord_2403322 prefixEnd_2403322 1234059353524951225322329 := by
  unfold tailWord_2403322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21914088649795580891185055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58437569732788215709826813 21914088649795580891185055)
  ·
    refine ⟨32871132974693371336777583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21914088649795580891185055 32871132974693371336777583)
    ·
      refine ⟨49306699462040057005166375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32871132974693371336777583 49306699462040057005166375)
      ·
        refine ⟨73960049193060085507749563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49306699462040057005166375 73960049193060085507749563)
        ·
          refine ⟨110940073789590128261624345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73960049193060085507749563 110940073789590128261624345)
          ·
            refine ⟨83205055342192596196218259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110940073789590128261624345 83205055342192596196218259)
            ·
              refine ⟨124807583013288894294327389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83205055342192596196218259 124807583013288894294327389)
              ·
                refine ⟨46802843629983335360372771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124807583013288894294327389 46802843629983335360372771)
                ·
                  refine ⟨70204265444975003040559157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46802843629983335360372771 70204265444975003040559157)
                  ·
                    refine ⟨6581649885466406535052421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70204265444975003040559157 6581649885466406535052421)
                    ·
                      refine ⟨1234059353524951225322329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6581649885466406535052421 1234059353524951225322329)
                      ·
                        rfl

theorem cell23_2403322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_2403322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403322 prefixEnd_2403322 := by exact prefixLift 2403322
  have htrace : WordTrace (prefixWord ++ tailWord_2403322) baseStart_2403322 baseEnd_2403322 := by
    simpa [prefixWord, tailWord_2403322, baseEnd_2403322] using wordTrace_append hprefix tailTrace_2403322
  have hstable : (prefixWord ++ tailWord_2403322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403322).length < 2 ^ (prefixWord ++ tailWord_2403322).sum := by decide
  have hdescent : baseEnd_2403322 < baseStart_2403322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403330 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2403330 : Nat := 118140960795 + 2403330 * 2 ^ 59
def prefixEnd_2403330 : Nat := 4983230072969 + 3 ^ 40 * 2403330 * 2
def baseEnd_2403330 : Nat := 1234063461370187194022293

theorem tailTrace_2403330 : CollatzResearch.WordTrace tailWord_2403330 prefixEnd_2403330 1234063461370187194022293 := by
  unfold tailWord_2403330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21914161595788335232757861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58437764255435560620687629 21914161595788335232757861)
  ·
    refine ⟨4108905299210312856142099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21914161595788335232757861 4108905299210312856142099)
    ·
      refine ⟨6163357948815469284213149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108905299210312856142099 6163357948815469284213149)
      ·
        refine ⟨2311259230805800981579931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6163357948815469284213149 2311259230805800981579931)
        ·
          refine ⟨3466888846208701472369897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311259230805800981579931 3466888846208701472369897)
          ·
            refine ⟨2600166634656526104277423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466888846208701472369897 2600166634656526104277423)
            ·
              refine ⟨3900249951984789156416135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600166634656526104277423 3900249951984789156416135)
              ·
                refine ⟨5850374927977183734624203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900249951984789156416135 5850374927977183734624203)
                ·
                  refine ⟨8775562391965775601936305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850374927977183734624203 8775562391965775601936305)
                  ·
                    refine ⟨6581671793974331701452229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8775562391965775601936305 6581671793974331701452229)
                    ·
                      refine ⟨1234063461370187194022293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6581671793974331701452229 1234063461370187194022293)
                      ·
                        rfl

theorem cell23_2403330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2403330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403330 prefixEnd_2403330 := by exact prefixLift 2403330
  have htrace : WordTrace (prefixWord ++ tailWord_2403330) baseStart_2403330 baseEnd_2403330 := by
    simpa [prefixWord, tailWord_2403330, baseEnd_2403330] using wordTrace_append hprefix tailTrace_2403330
  have hstable : (prefixWord ++ tailWord_2403330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403330).length < 2 ^ (prefixWord ++ tailWord_2403330).sum := by decide
  have hdescent : baseEnd_2403330 < baseStart_2403330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403333 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_2403333 : Nat := 118140960795 + 2403333 * 2 ^ 59
def prefixEnd_2403333 : Nat := 4983230072969 + 3 ^ 40 * 2403333 * 2
def baseEnd_2403333 : Nat := 1234065001812150682284779

theorem tailTrace_2403333 : CollatzResearch.WordTrace tailWord_2403333 prefixEnd_2403333 1234065001812150682284779 := by
  unfold tailWord_2403333
  simp only [CollatzResearch.WordTrace]
  refine ⟨87656755802142472443390653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58437837201428314962260435 87656755802142472443390653)
  ·
    refine ⟨32871283425803427166271495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87656755802142472443390653 32871283425803427166271495)
    ·
      refine ⟨49306925138705140749407243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32871283425803427166271495 49306925138705140749407243)
      ·
        refine ⟨73960387708057711124110865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49306925138705140749407243 73960387708057711124110865)
        ·
          refine ⟨55470290781043283343083149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73960387708057711124110865 55470290781043283343083149)
          ·
            refine ⟨20801359042891231253656181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55470290781043283343083149 20801359042891231253656181)
            ·
              refine ⟨1950127410271052930030267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20801359042891231253656181 1950127410271052930030267)
              ·
                refine ⟨2925191115406579395045401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950127410271052930030267 2925191115406579395045401)
                ·
                  refine ⟨2193893336554934546284051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925191115406579395045401 2193893336554934546284051)
                  ·
                    refine ⟨3290840004832401819426077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2193893336554934546284051 3290840004832401819426077)
                    ·
                      refine ⟨1234065001812150682284779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3290840004832401819426077 1234065001812150682284779)
                      ·
                        rfl

theorem cell23_2403333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_2403333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403333 prefixEnd_2403333 := by exact prefixLift 2403333
  have htrace : WordTrace (prefixWord ++ tailWord_2403333) baseStart_2403333 baseEnd_2403333 := by
    simpa [prefixWord, tailWord_2403333, baseEnd_2403333] using wordTrace_append hprefix tailTrace_2403333
  have hstable : (prefixWord ++ tailWord_2403333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403333).length < 2 ^ (prefixWord ++ tailWord_2403333).sum := by decide
  have hdescent : baseEnd_2403333 < baseStart_2403333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403359 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2403359 : Nat := 118140960795 + 2403359 * 2 ^ 59
def prefixEnd_2403359 : Nat := 4983230072969 + 3 ^ 40 * 2403359 * 2
def baseEnd_2403359 : Nat := 1234078352309167580559659

theorem tailTrace_2403359 : CollatzResearch.WordTrace tailWord_2403359 prefixEnd_2403359 1234078352309167580559659 := by
  unfold tailWord_2403359
  simp only [CollatzResearch.WordTrace]
  refine ⟨87657704100048278883837131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58438469400032185922558087 87657704100048278883837131)
  ·
    refine ⟨131486556150072418325755697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87657704100048278883837131 131486556150072418325755697)
    ·
      refine ⟨98614917112554313744316773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131486556150072418325755697 98614917112554313744316773)
      ·
        refine ⟨18490296958603933827059395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98614917112554313744316773 18490296958603933827059395)
        ·
          refine ⟨27735445437905900740589093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18490296958603933827059395 27735445437905900740589093)
          ·
            refine ⟨5200396019607356388860455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27735445437905900740589093 5200396019607356388860455)
            ·
              refine ⟨7800594029411034583290683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200396019607356388860455 7800594029411034583290683)
              ·
                refine ⟨11700891044116551874936025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7800594029411034583290683 11700891044116551874936025)
                ·
                  refine ⟨8775668283087413906202019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11700891044116551874936025 8775668283087413906202019)
                  ·
                    refine ⟨13163502424631120859303029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8775668283087413906202019 13163502424631120859303029)
                    ·
                      refine ⟨1234078352309167580559659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13163502424631120859303029 1234078352309167580559659)
                      ·
                        rfl

theorem cell23_2403359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2403359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403359 prefixEnd_2403359 := by exact prefixLift 2403359
  have htrace : WordTrace (prefixWord ++ tailWord_2403359) baseStart_2403359 baseEnd_2403359 := by
    simpa [prefixWord, tailWord_2403359, baseEnd_2403359] using wordTrace_append hprefix tailTrace_2403359
  have hstable : (prefixWord ++ tailWord_2403359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403359).length < 2 ^ (prefixWord ++ tailWord_2403359).sum := by decide
  have hdescent : baseEnd_2403359 < baseStart_2403359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403372 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2403372 : Nat := 118140960795 + 2403372 * 2 ^ 59
def prefixEnd_2403372 : Nat := 4983230072969 + 3 ^ 40 * 2403372 * 2
def baseEnd_2403372 : Nat := 1234085027557676029697099

theorem tailTrace_2403372 : CollatzResearch.WordTrace tailWord_2403372 prefixEnd_2403372 1234085027557676029697099 := by
  unfold tailWord_2403372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43829089124500591052030185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58438785499334121402706913 43829089124500591052030185)
  ·
    refine ⟨32871816843375443289022639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43829089124500591052030185 32871816843375443289022639)
    ·
      refine ⟨49307725265063164933533959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32871816843375443289022639 49307725265063164933533959)
      ·
        refine ⟨73961587897594747400300939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49307725265063164933533959 73961587897594747400300939)
        ·
          refine ⟨110942381846392121100451409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73961587897594747400300939 110942381846392121100451409)
          ·
            refine ⟨83206786384794090825338557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110942381846392121100451409 83206786384794090825338557)
            ·
              refine ⟨31202544894297784059501959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83206786384794090825338557 31202544894297784059501959)
              ·
                refine ⟨46803817341446676089252939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31202544894297784059501959 46803817341446676089252939)
                ·
                  refine ⟨70205726012170014133879409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46803817341446676089252939 70205726012170014133879409)
                  ·
                    refine ⟨52654294509127510600409557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70205726012170014133879409 52654294509127510600409557)
                    ·
                      refine ⟨1234085027557676029697099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52654294509127510600409557 1234085027557676029697099)
                      ·
                        rfl

theorem cell23_2403372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2403372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403372 prefixEnd_2403372 := by exact prefixLift 2403372
  have htrace : WordTrace (prefixWord ++ tailWord_2403372) baseStart_2403372 baseEnd_2403372 := by
    simpa [prefixWord, tailWord_2403372, baseEnd_2403372] using wordTrace_append hprefix tailTrace_2403372
  have hstable : (prefixWord ++ tailWord_2403372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403372).length < 2 ^ (prefixWord ++ tailWord_2403372).sum := by decide
  have hdescent : baseEnd_2403372 < baseStart_2403372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403409 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_2403409 : Nat := 118140960795 + 2403409 * 2 ^ 59
def prefixEnd_2403409 : Nat := 4983230072969 + 3 ^ 40 * 2403409 * 2
def baseEnd_2403409 : Nat := 411368008780630794978143

theorem tailTrace_2403409 : CollatzResearch.WordTrace tailWord_2403409 prefixEnd_2403409 411368008780630794978143 := by
  unfold tailWord_2403409
  simp only [CollatzResearch.WordTrace]
  refine ⟨87659527749867137423157281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58439685166578091615438187 87659527749867137423157281)
  ·
    refine ⟨65744645812400353067367961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87659527749867137423157281 65744645812400353067367961)
    ·
      refine ⟨49308484359300264800525971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65744645812400353067367961 49308484359300264800525971)
      ·
        refine ⟨73962726538950397200788957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49308484359300264800525971 73962726538950397200788957)
        ·
          refine ⟨27736022452106398950295859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73962726538950397200788957 27736022452106398950295859)
          ·
            refine ⟨41604033678159598425443789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27736022452106398950295859 41604033678159598425443789)
            ·
              refine ⟨15601512629309849409541421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41604033678159598425443789 15601512629309849409541421)
              ·
                refine ⟨5850567235991193528578033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15601512629309849409541421 5850567235991193528578033)
                ·
                  refine ⟨4387925426993395146433525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850567235991193528578033 4387925426993395146433525)
                  ·
                    refine ⟨411368008780630794978143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4387925426993395146433525 411368008780630794978143)
                    ·
                      rfl

theorem cell23_2403409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_2403409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403409 prefixEnd_2403409 := by exact prefixLift 2403409
  have htrace : WordTrace (prefixWord ++ tailWord_2403409) baseStart_2403409 baseEnd_2403409 := by
    simpa [prefixWord, tailWord_2403409, baseEnd_2403409] using wordTrace_append hprefix tailTrace_2403409
  have hstable : (prefixWord ++ tailWord_2403409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403409).length < 2 ^ (prefixWord ++ tailWord_2403409).sum := by decide
  have hdescent : baseEnd_2403409 < baseStart_2403409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403446 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2403446 : Nat := 118140960795 + 2403446 * 2 ^ 59
def prefixEnd_2403446 : Nat := 4983230072969 + 3 ^ 40 * 2403446 * 2
def baseEnd_2403446 : Nat := 1234123025126108740171759

theorem tailTrace_2403446 : CollatzResearch.WordTrace tailWord_2403446 prefixEnd_2403446 1234123025126108740171759 := by
  unfold tailWord_2403446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478804828170818296390887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58440584833822061828169461 5478804828170818296390887)
  ·
    refine ⟨8218207242256227444586331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5478804828170818296390887 8218207242256227444586331)
    ·
      refine ⟨12327310863384341166879497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8218207242256227444586331 12327310863384341166879497)
      ·
        refine ⟨9245483147538255875159623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12327310863384341166879497 9245483147538255875159623)
        ·
          refine ⟨13868224721307383812739435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245483147538255875159623 13868224721307383812739435)
          ·
            refine ⟨20802337081961075719109153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868224721307383812739435 20802337081961075719109153)
            ·
              refine ⟨15601752811470806789331865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20802337081961075719109153 15601752811470806789331865)
              ·
                refine ⟨11701314608603105091998899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15601752811470806789331865 11701314608603105091998899)
                ·
                  refine ⟨17551971912904657637998349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11701314608603105091998899 17551971912904657637998349)
                  ·
                    refine ⟨6581989467339246614249381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17551971912904657637998349 6581989467339246614249381)
                    ·
                      refine ⟨1234123025126108740171759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6581989467339246614249381 1234123025126108740171759)
                      ·
                        rfl

theorem cell23_2403446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2403446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403446 prefixEnd_2403446 := by exact prefixLift 2403446
  have htrace : WordTrace (prefixWord ++ tailWord_2403446) baseStart_2403446 baseEnd_2403446 := by
    simpa [prefixWord, tailWord_2403446, baseEnd_2403446] using wordTrace_append hprefix tailTrace_2403446
  have hstable : (prefixWord ++ tailWord_2403446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403446).length < 2 ^ (prefixWord ++ tailWord_2403446).sum := by decide
  have hdescent : baseEnd_2403446 < baseStart_2403446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403466 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2403466 : Nat := 118140960795 + 2403466 * 2 ^ 59
def prefixEnd_2403466 : Nat := 4983230072969 + 3 ^ 40 * 2403466 * 2
def baseEnd_2403466 : Nat := 1234133294739198661921667

theorem tailTrace_2403466 : CollatzResearch.WordTrace tailWord_2403466 prefixEnd_2403466 1234133294739198661921667 := by
  unfold tailWord_2403466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21915401677665159039495563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58441071140440424105321501 21915401677665159039495563)
  ·
    refine ⟨32873102516497738559243345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21915401677665159039495563 32873102516497738559243345)
    ·
      refine ⟨24654826887373303919432509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32873102516497738559243345 24654826887373303919432509)
      ·
        refine ⟨9245560082764988969787191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24654826887373303919432509 9245560082764988969787191)
        ·
          refine ⟨13868340124147483454680787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245560082764988969787191 13868340124147483454680787)
          ·
            refine ⟨20802510186221225182021181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868340124147483454680787 20802510186221225182021181)
            ·
              refine ⟨7800941319832959443257943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20802510186221225182021181 7800941319832959443257943)
              ·
                refine ⟨11701411979749439164886915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7800941319832959443257943 11701411979749439164886915)
                ·
                  refine ⟨17552117969624158747330373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11701411979749439164886915 17552117969624158747330373)
                  ·
                    refine ⟨3291022119304529765124445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17552117969624158747330373 3291022119304529765124445)
                    ·
                      refine ⟨1234133294739198661921667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291022119304529765124445 1234133294739198661921667)
                      ·
                        rfl

theorem cell23_2403466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2403466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403466 prefixEnd_2403466 := by exact prefixLift 2403466
  have htrace : WordTrace (prefixWord ++ tailWord_2403466) baseStart_2403466 baseEnd_2403466 := by
    simpa [prefixWord, tailWord_2403466, baseEnd_2403466] using wordTrace_append hprefix tailTrace_2403466
  have hstable : (prefixWord ++ tailWord_2403466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403466).length < 2 ^ (prefixWord ++ tailWord_2403466).sum := by decide
  have hdescent : baseEnd_2403466 < baseStart_2403466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403489 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2403489 : Nat := 118140960795 + 2403489 * 2 ^ 59
def prefixEnd_2403489 : Nat := 4983230072969 + 3 ^ 40 * 2403489 * 2
def baseEnd_2403489 : Nat := 1234145104794252071934061

theorem tailTrace_2403489 : CollatzResearch.WordTrace tailWord_2403489 prefixEnd_2403489 1234145104794252071934061 := by
  unfold tailWord_2403489
  simp only [CollatzResearch.WordTrace]
  refine ⟨87662445589577311086069521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58441630393051540724046347 87662445589577311086069521)
  ·
    refine ⟨65746834192182983314552141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87662445589577311086069521 65746834192182983314552141)
    ·
      refine ⟨24655062822068618742957053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65746834192182983314552141 24655062822068618742957053)
      ·
        refine ⟨9245648558275732028608895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24655062822068618742957053 9245648558275732028608895)
        ·
          refine ⟨13868472837413598042913343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245648558275732028608895 13868472837413598042913343)
          ·
            refine ⟨20802709256120397064370015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868472837413598042913343 20802709256120397064370015)
            ·
              refine ⟨31204063884180595596555023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20802709256120397064370015 31204063884180595596555023)
              ·
                refine ⟨46806095826270893394832535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31204063884180595596555023 46806095826270893394832535)
                ·
                  refine ⟨70209143739406340092248803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46806095826270893394832535 70209143739406340092248803)
                  ·
                    refine ⟨105313715609109510138373205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70209143739406340092248803 105313715609109510138373205)
                    ·
                      refine ⟨1234145104794252071934061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 105313715609109510138373205 1234145104794252071934061)
                      ·
                        rfl

theorem cell23_2403489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2403489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403489 prefixEnd_2403489 := by exact prefixLift 2403489
  have htrace : WordTrace (prefixWord ++ tailWord_2403489) baseStart_2403489 baseEnd_2403489 := by
    simpa [prefixWord, tailWord_2403489, baseEnd_2403489] using wordTrace_append hprefix tailTrace_2403489
  have hstable : (prefixWord ++ tailWord_2403489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403489).length < 2 ^ (prefixWord ++ tailWord_2403489).sum := by decide
  have hdescent : baseEnd_2403489 < baseStart_2403489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403490 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2403490 : Nat := 118140960795 + 2403490 * 2 ^ 59
def prefixEnd_2403490 : Nat := 4983230072969 + 3 ^ 40 * 2403490 * 2
def baseEnd_2403490 : Nat := 411381872758302189340519

theorem tailTrace_2403490 : CollatzResearch.WordTrace tailWord_2403490 prefixEnd_2403490 411381872758302189340519 := by
  unfold tailWord_2403490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21915620515643422064213981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58441654708382458837903949 21915620515643422064213981)
  ·
    refine ⟨8218357693366283274080243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21915620515643422064213981 8218357693366283274080243)
    ·
      refine ⟨12327536540049424911120365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8218357693366283274080243 12327536540049424911120365)
      ·
        refine ⟨4622826202518534341670137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12327536540049424911120365 4622826202518534341670137)
        ·
          refine ⟨3467119651888900756252603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4622826202518534341670137 3467119651888900756252603)
          ·
            refine ⟨5200679477833351134378905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467119651888900756252603 5200679477833351134378905)
            ·
              refine ⟨3900509608375013350784179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5200679477833351134378905 3900509608375013350784179)
              ·
                refine ⟨5850764412562520026176269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900509608375013350784179 5850764412562520026176269)
                ·
                  refine ⟨2194036654710945009816101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5850764412562520026176269 2194036654710945009816101)
                  ·
                    refine ⟨411381872758302189340519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194036654710945009816101 411381872758302189340519)
                    ·
                      rfl

theorem cell23_2403490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2403490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403490 prefixEnd_2403490 := by exact prefixLift 2403490
  have htrace : WordTrace (prefixWord ++ tailWord_2403490) baseStart_2403490 baseEnd_2403490 := by
    simpa [prefixWord, tailWord_2403490, baseEnd_2403490] using wordTrace_append hprefix tailTrace_2403490
  have hstable : (prefixWord ++ tailWord_2403490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403490).length < 2 ^ (prefixWord ++ tailWord_2403490).sum := by decide
  have hdescent : baseEnd_2403490 < baseStart_2403490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403513 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2403513 : Nat := 118140960795 + 2403513 * 2 ^ 59
def prefixEnd_2403513 : Nat := 4983230072969 + 3 ^ 40 * 2403513 * 2
def baseEnd_2403513 : Nat := 1234157428329959978033951

theorem tailTrace_2403513 : CollatzResearch.WordTrace tailWord_2403513 prefixEnd_2403513 1234157428329959978033951 := by
  unfold tailWord_2403513
  simp only [CollatzResearch.WordTrace]
  refine ⟨87663320941490363184943193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58442213960993575456628795 87663320941490363184943193)
  ·
    refine ⟨65747490706117772388707395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87663320941490363184943193 65747490706117772388707395)
    ·
      refine ⟨98621236059176658583061093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65747490706117772388707395 98621236059176658583061093)
      ·
        refine ⟨18491481761095623484323955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98621236059176658583061093 18491481761095623484323955)
        ·
          refine ⟨27737222641643435226485933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18491481761095623484323955 27737222641643435226485933)
          ·
            refine ⟨10401458490616288209932225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27737222641643435226485933 10401458490616288209932225)
            ·
              refine ⟨7801093867962216157449169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10401458490616288209932225 7801093867962216157449169)
              ·
                refine ⟨5850820400971662118086877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7801093867962216157449169 5850820400971662118086877)
                ·
                  refine ⟨2194057650364373294282579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5850820400971662118086877 2194057650364373294282579)
                  ·
                    refine ⟨3291086475546559941423869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2194057650364373294282579 3291086475546559941423869)
                    ·
                      refine ⟨1234157428329959978033951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291086475546559941423869 1234157428329959978033951)
                      ·
                        rfl

theorem cell23_2403513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2403513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403513 prefixEnd_2403513 := by exact prefixLift 2403513
  have htrace : WordTrace (prefixWord ++ tailWord_2403513) baseStart_2403513 baseEnd_2403513 := by
    simpa [prefixWord, tailWord_2403513, baseEnd_2403513] using wordTrace_append hprefix tailTrace_2403513
  have hstable : (prefixWord ++ tailWord_2403513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403513).length < 2 ^ (prefixWord ++ tailWord_2403513).sum := by decide
  have hdescent : baseEnd_2403513 < baseStart_2403513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403524 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2403524 : Nat := 118140960795 + 2403524 * 2 ^ 59
def prefixEnd_2403524 : Nat := 4983230072969 + 3 ^ 40 * 2403524 * 2
def baseEnd_2403524 : Nat := 411387692205719811665467

theorem tailTrace_2403524 : CollatzResearch.WordTrace tailWord_2403524 prefixEnd_2403524 411387692205719811665467 := by
  unfold tailWord_2403524
  simp only [CollatzResearch.WordTrace]
  refine ⟨43831861072225256031796813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58442481429633674709062417 43831861072225256031796813)
  ·
    refine ⟨16436947902084471011923805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43831861072225256031796813 16436947902084471011923805)
    ·
      refine ⟨6163855463281676629471427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16436947902084471011923805 6163855463281676629471427)
      ·
        refine ⟨9245783194922514944207141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163855463281676629471427 9245783194922514944207141)
        ·
          refine ⟨1733584349047971552038839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9245783194922514944207141 1733584349047971552038839)
          ·
            refine ⟨2600376523571957328058259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733584349047971552038839 2600376523571957328058259)
            ·
              refine ⟨3900564785357935992087389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600376523571957328058259 3900564785357935992087389)
              ·
                refine ⟨1462711794509225997032771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3900564785357935992087389 1462711794509225997032771)
                ·
                  refine ⟨2194067691763838995549157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462711794509225997032771 2194067691763838995549157)
                  ·
                    refine ⟨411387692205719811665467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194067691763838995549157 411387692205719811665467)
                    ·
                      rfl

theorem cell23_2403524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2403524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403524 prefixEnd_2403524 := by exact prefixLift 2403524
  have htrace : WordTrace (prefixWord ++ tailWord_2403524) baseStart_2403524 baseEnd_2403524 := by
    simpa [prefixWord, tailWord_2403524, baseEnd_2403524] using wordTrace_append hprefix tailTrace_2403524
  have hstable : (prefixWord ++ tailWord_2403524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403524).length < 2 ^ (prefixWord ++ tailWord_2403524).sum := by decide
  have hdescent : baseEnd_2403524 < baseStart_2403524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_2403539 : Nat := 118140960795 + 2403539 * 2 ^ 59
def prefixEnd_2403539 : Nat := 4983230072969 + 3 ^ 40 * 2403539 * 2
def baseEnd_2403539 : Nat := 1234170778826976876308831

theorem tailTrace_2403539 : CollatzResearch.WordTrace tailWord_2403539 prefixEnd_2403539 1234170778826976876308831 := by
  unfold tailWord_2403539
  simp only [CollatzResearch.WordTrace]
  refine ⟨87664269239396169625389671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58442846159597446416926447 87664269239396169625389671)
  ·
    refine ⟨131496403859094254438084507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87664269239396169625389671 131496403859094254438084507)
    ·
      refine ⟨197244605788641381657126761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131496403859094254438084507 197244605788641381657126761)
      ·
        refine ⟨147933454341481036242845071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197244605788641381657126761 147933454341481036242845071)
        ·
          refine ⟨221900181512221554364267607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147933454341481036242845071 221900181512221554364267607)
          ·
            refine ⟨332850272268332331546401411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221900181512221554364267607 332850272268332331546401411)
            ·
              refine ⟨499275408402498497319602117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332850272268332331546401411 499275408402498497319602117)
              ·
                refine ⟨93614139075468468247425397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499275408402498497319602117 93614139075468468247425397)
                ·
                  refine ⟨8776325538325168898196131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93614139075468468247425397 8776325538325168898196131)
                  ·
                    refine ⟨13164488307487753347294197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8776325538325168898196131 13164488307487753347294197)
                    ·
                      refine ⟨1234170778826976876308831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13164488307487753347294197 1234170778826976876308831)
                      ·
                        rfl

theorem cell23_2403539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_2403539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403539 prefixEnd_2403539 := by exact prefixLift 2403539
  have htrace : WordTrace (prefixWord ++ tailWord_2403539) baseStart_2403539 baseEnd_2403539 := by
    simpa [prefixWord, tailWord_2403539, baseEnd_2403539] using wordTrace_append hprefix tailTrace_2403539
  have hstable : (prefixWord ++ tailWord_2403539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403539).length < 2 ^ (prefixWord ++ tailWord_2403539).sum := by decide
  have hdescent : baseEnd_2403539 < baseStart_2403539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403556 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_2403556 : Nat := 118140960795 + 2403556 * 2 ^ 59
def prefixEnd_2403556 : Nat := 4983230072969 + 3 ^ 40 * 2403556 * 2
def baseEnd_2403556 : Nat := 1234179507998103309796253

theorem tailTrace_2403556 : CollatzResearch.WordTrace tailWord_2403556 prefixEnd_2403556 1234179507998103309796253 := by
  unfold tailWord_2403556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43832444640167290764379261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58443259520223054352505681 43832444640167290764379261)
  ·
    refine ⟨16437166740062734036642223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43832444640167290764379261 16437166740062734036642223)
    ·
      refine ⟨24655750110094101054963335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16437166740062734036642223 24655750110094101054963335)
      ·
        refine ⟨36983625165141151582445003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24655750110094101054963335 36983625165141151582445003)
        ·
          refine ⟨55475437747711727373667505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36983625165141151582445003 55475437747711727373667505)
          ·
            refine ⟨41606578310783795530250629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55475437747711727373667505 41606578310783795530250629)
            ·
              refine ⟨7801233433271961661921993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41606578310783795530250629 7801233433271961661921993)
              ·
                refine ⟨5850925074953971246441495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7801233433271961661921993 5850925074953971246441495)
                ·
                  refine ⟨8776387612430956869662243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5850925074953971246441495 8776387612430956869662243)
                  ·
                    refine ⟨13164581418646435304493365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8776387612430956869662243 13164581418646435304493365)
                    ·
                      refine ⟨1234179507998103309796253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13164581418646435304493365 1234179507998103309796253)
                      ·
                        rfl

theorem cell23_2403556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_2403556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403556 prefixEnd_2403556 := by exact prefixLift 2403556
  have htrace : WordTrace (prefixWord ++ tailWord_2403556) baseStart_2403556 baseEnd_2403556 := by
    simpa [prefixWord, tailWord_2403556, baseEnd_2403556] using wordTrace_append hprefix tailTrace_2403556
  have hstable : (prefixWord ++ tailWord_2403556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403556).length < 2 ^ (prefixWord ++ tailWord_2403556).sum := by decide
  have hdescent : baseEnd_2403556 < baseStart_2403556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403563 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 2, 4]
def baseStart_2403563 : Nat := 118140960795 + 2403563 * 2 ^ 59
def prefixEnd_2403563 : Nat := 4983230072969 + 3 ^ 40 * 2403563 * 2
def baseEnd_2403563 : Nat := 411394367454228260802907

theorem tailTrace_2403563 : CollatzResearch.WordTrace tailWord_2403563 prefixEnd_2403563 411394367454228260802907 := by
  unfold tailWord_2403563
  simp only [CollatzResearch.WordTrace]
  refine ⟨87665144591309221724263343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58443429727539481149508895 87665144591309221724263343)
  ·
    refine ⟨131497716886963832586395015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87665144591309221724263343 131497716886963832586395015)
    ·
      refine ⟨197246575330445748879592523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131497716886963832586395015 197246575330445748879592523)
      ·
        refine ⟨295869862995668623319388785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197246575330445748879592523 295869862995668623319388785)
        ·
          refine ⟨221902397246751467489541589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295869862995668623319388785 221902397246751467489541589)
          ·
            refine ⟨5200837435470737519286131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 221902397246751467489541589 5200837435470737519286131)
            ·
              refine ⟨7801256153206106278929197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5200837435470737519286131 7801256153206106278929197)
              ·
                refine ⟨2925471057452289854598449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7801256153206106278929197 2925471057452289854598449)
                ·
                  refine ⟨2194103293089217390948837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925471057452289854598449 2194103293089217390948837)
                  ·
                    refine ⟨411394367454228260802907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194103293089217390948837 411394367454228260802907)
                    ·
                      rfl

theorem cell23_2403563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 4].length) (baseStart_2403563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403563 prefixEnd_2403563 := by exact prefixLift 2403563
  have htrace : WordTrace (prefixWord ++ tailWord_2403563) baseStart_2403563 baseEnd_2403563 := by
    simpa [prefixWord, tailWord_2403563, baseEnd_2403563] using wordTrace_append hprefix tailTrace_2403563
  have hstable : (prefixWord ++ tailWord_2403563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403563).length < 2 ^ (prefixWord ++ tailWord_2403563).sum := by decide
  have hdescent : baseEnd_2403563 < baseStart_2403563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403566 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2403566 : Nat := 118140960795 + 2403566 * 2 ^ 59
def prefixEnd_2403566 : Nat := 4983230072969 + 3 ^ 40 * 2403566 * 2
def baseEnd_2403566 : Nat := 1234184642804648270671207

theorem tailTrace_2403566 : CollatzResearch.WordTrace tailWord_2403566 prefixEnd_2403566 1234184642804648270671207 := by
  unfold tailWord_2403566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958156751287294154577819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58443502673532235491081701 10958156751287294154577819)
  ·
    refine ⟨16437235126930941231866729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10958156751287294154577819 16437235126930941231866729)
    ·
      refine ⟨12327926345198205923900047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16437235126930941231866729 12327926345198205923900047)
      ·
        refine ⟨18491889517797308885850071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327926345198205923900047 18491889517797308885850071)
        ·
          refine ⟨27737834276695963328775107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18491889517797308885850071 27737834276695963328775107)
          ·
            refine ⟨41606751415043944993162661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27737834276695963328775107 41606751415043944993162661)
            ·
              refine ⟨7801265890320739686217999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41606751415043944993162661 7801265890320739686217999)
              ·
                refine ⟨11701898835481109529326999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7801265890320739686217999 11701898835481109529326999)
                ·
                  refine ⟨17552848253221664293990499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11701898835481109529326999 17552848253221664293990499)
                  ·
                    refine ⟨26329272379832496440985749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17552848253221664293990499 26329272379832496440985749)
                    ·
                      refine ⟨1234184642804648270671207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26329272379832496440985749 1234184642804648270671207)
                      ·
                        rfl

theorem cell23_2403566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2403566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403566 prefixEnd_2403566 := by exact prefixLift 2403566
  have htrace : WordTrace (prefixWord ++ tailWord_2403566) baseStart_2403566 baseEnd_2403566 := by
    simpa [prefixWord, tailWord_2403566, baseEnd_2403566] using wordTrace_append hprefix tailTrace_2403566
  have hstable : (prefixWord ++ tailWord_2403566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403566).length < 2 ^ (prefixWord ++ tailWord_2403566).sum := by decide
  have hdescent : baseEnd_2403566 < baseStart_2403566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403599 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_2403599 : Nat := 118140960795 + 2403599 * 2 ^ 59
def prefixEnd_2403599 : Nat := 4983230072969 + 3 ^ 40 * 2403599 * 2
def baseEnd_2403599 : Nat := 1234201587666246641558555

theorem tailTrace_2403599 : CollatzResearch.WordTrace tailWord_2403599 prefixEnd_2403599 1234201587666246641558555 := by
  unfold tailWord_2403599
  simp only [CollatzResearch.WordTrace]
  refine ⟨87666457619178799872573851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58444305079452533248382567 87666457619178799872573851)
  ·
    refine ⟨131499686428768199808860777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87666457619178799872573851 131499686428768199808860777)
    ·
      refine ⟨98624764821576149856645583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131499686428768199808860777 98624764821576149856645583)
      ·
        refine ⟨147937147232364224784968375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98624764821576149856645583 147937147232364224784968375)
        ·
          refine ⟨221905720848546337177452563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147937147232364224784968375 221905720848546337177452563)
          ·
            refine ⟨332858581272819505766178845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221905720848546337177452563 332858581272819505766178845)
            ·
              refine ⟨124821967977307314662317067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332858581272819505766178845 124821967977307314662317067)
              ·
                refine ⟨187232951965960971993475601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124821967977307314662317067 187232951965960971993475601)
                ·
                  refine ⟨140424713974470728995106701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187232951965960971993475601 140424713974470728995106701)
                  ·
                    refine ⟨52659267740426523373165013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140424713974470728995106701 52659267740426523373165013)
                    ·
                      refine ⟨1234201587666246641558555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52659267740426523373165013 1234201587666246641558555)
                      ·
                        rfl

theorem cell23_2403599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_2403599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403599 prefixEnd_2403599 := by exact prefixLift 2403599
  have htrace : WordTrace (prefixWord ++ tailWord_2403599) baseStart_2403599 baseEnd_2403599 := by
    simpa [prefixWord, tailWord_2403599, baseEnd_2403599] using wordTrace_append hprefix tailTrace_2403599
  have hstable : (prefixWord ++ tailWord_2403599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403599).length < 2 ^ (prefixWord ++ tailWord_2403599).sum := by decide
  have hdescent : baseEnd_2403599 < baseStart_2403599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403620 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_2403620 : Nat := 118140960795 + 2403620 * 2 ^ 59
def prefixEnd_2403620 : Nat := 4983230072969 + 3 ^ 40 * 2403620 * 2
def baseEnd_2403620 : Nat := 1234212370759991059395959

theorem tailTrace_2403620 : CollatzResearch.WordTrace tailWord_2403620 prefixEnd_2403620 1234212370759991059395959 := by
  unfold tailWord_2403620
  simp only [CollatzResearch.WordTrace]
  refine ⟨43833611776051360229544157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58444815701401813639392209 43833611776051360229544157)
  ·
    refine ⟨16437604416019260086079059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43833611776051360229544157 16437604416019260086079059)
    ·
      refine ⟨24656406624028890129118589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16437604416019260086079059 24656406624028890129118589)
      ·
        refine ⟨9246152484010833798419471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24656406624028890129118589 9246152484010833798419471)
        ·
          refine ⟨13869228726016250697629207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246152484010833798419471 13869228726016250697629207)
          ·
            refine ⟨20803843089024376046443811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13869228726016250697629207 20803843089024376046443811)
            ·
              refine ⟨31205764633536564069665717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20803843089024376046443811 31205764633536564069665717)
              ·
                refine ⟨2925540434394052881531161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31205764633536564069665717 2925540434394052881531161)
                ·
                  refine ⟨2194155325795539661148371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925540434394052881531161 2194155325795539661148371)
                  ·
                    refine ⟨3291232988693309491722557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2194155325795539661148371 3291232988693309491722557)
                    ·
                      refine ⟨1234212370759991059395959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291232988693309491722557 1234212370759991059395959)
                      ·
                        rfl

theorem cell23_2403620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_2403620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403620 prefixEnd_2403620 := by exact prefixLift 2403620
  have htrace : WordTrace (prefixWord ++ tailWord_2403620) baseStart_2403620 baseEnd_2403620 := by
    simpa [prefixWord, tailWord_2403620, baseEnd_2403620] using wordTrace_append hprefix tailTrace_2403620
  have hstable : (prefixWord ++ tailWord_2403620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403620).length < 2 ^ (prefixWord ++ tailWord_2403620).sum := by decide
  have hdescent : baseEnd_2403620 < baseStart_2403620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403638 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2403638 : Nat := 118140960795 + 2403638 * 2 ^ 59
def prefixEnd_2403638 : Nat := 4983230072969 + 3 ^ 40 * 2403638 * 2
def baseEnd_2403638 : Nat := 1234221613411771988970877

theorem tailTrace_2403638 : CollatzResearch.WordTrace tailWord_2403638 prefixEnd_2403638 1234221613411771988970877 := by
  unfold tailWord_2403638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479242504127344345827723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58445253377358339688829045 5479242504127344345827723)
  ·
    refine ⟨8218863756191016518741585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479242504127344345827723 8218863756191016518741585)
    ·
      refine ⟨6164147817143262389056189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8218863756191016518741585 6164147817143262389056189)
      ·
        refine ⟨2311555431428723395896071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6164147817143262389056189 2311555431428723395896071)
        ·
          refine ⟨3467333147143085093844107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311555431428723395896071 3467333147143085093844107)
          ·
            refine ⟨5200999720714627640766161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467333147143085093844107 5200999720714627640766161)
            ·
              refine ⟨3900749790535970730574621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5200999720714627640766161 3900749790535970730574621)
              ·
                refine ⟨1462781171450989023965483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3900749790535970730574621 1462781171450989023965483)
                ·
                  refine ⟨2194171757176483535948225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462781171450989023965483 2194171757176483535948225)
                  ·
                    refine ⟨1645628817882362651961169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194171757176483535948225 1645628817882362651961169)
                    ·
                      refine ⟨1234221613411771988970877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645628817882362651961169 1234221613411771988970877)
                      ·
                        rfl

theorem cell23_2403638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2403638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403638 prefixEnd_2403638 := by exact prefixLift 2403638
  have htrace : WordTrace (prefixWord ++ tailWord_2403638) baseStart_2403638 baseEnd_2403638 := by
    simpa [prefixWord, tailWord_2403638, baseEnd_2403638] using wordTrace_append hprefix tailTrace_2403638
  have hstable : (prefixWord ++ tailWord_2403638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403638).length < 2 ^ (prefixWord ++ tailWord_2403638).sum := by decide
  have hdescent : baseEnd_2403638 < baseStart_2403638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403647 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 1, 3, 2]
def baseStart_2403647 : Nat := 118140960795 + 2403647 * 2 ^ 59
def prefixEnd_2403647 : Nat := 4983230072969 + 3 ^ 40 * 2403647 * 2
def baseEnd_2403647 : Nat := 1234226234737662453758335

theorem tailTrace_2403647 : CollatzResearch.WordTrace tailWord_2403647 prefixEnd_2403647 1234226234737662453758335 := by
  unfold tailWord_2403647
  simp only [CollatzResearch.WordTrace]
  refine ⟨87668208323004904070321195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58445472215336602713547463 87668208323004904070321195)
  ·
    refine ⟨131502312484507356105481793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87668208323004904070321195 131502312484507356105481793)
    ·
      refine ⟨98626734363380517079111345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131502312484507356105481793 98626734363380517079111345)
      ·
        refine ⟨73970050772535387809333509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98626734363380517079111345 73970050772535387809333509)
        ·
          refine ⟨13869384519850385214250033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73970050772535387809333509 13869384519850385214250033)
          ·
            refine ⟨10402038389887788910687525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13869384519850385214250033 10402038389887788910687525)
            ·
              refine ⟨1950382198103960420753911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10402038389887788910687525 1950382198103960420753911)
              ·
                refine ⟨2925573297155940631130867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950382198103960420753911 2925573297155940631130867)
                ·
                  refine ⟨4388359945733910946696301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925573297155940631130867 4388359945733910946696301)
                  ·
                    refine ⟨1645634979650216605011113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4388359945733910946696301 1645634979650216605011113)
                    ·
                      refine ⟨1234226234737662453758335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645634979650216605011113 1234226234737662453758335)
                      ·
                        rfl

theorem cell23_2403647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_2403647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403647 prefixEnd_2403647 := by exact prefixLift 2403647
  have htrace : WordTrace (prefixWord ++ tailWord_2403647) baseStart_2403647 baseEnd_2403647 := by
    simpa [prefixWord, tailWord_2403647, baseEnd_2403647] using wordTrace_append hprefix tailTrace_2403647
  have hstable : (prefixWord ++ tailWord_2403647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403647).length < 2 ^ (prefixWord ++ tailWord_2403647).sum := by decide
  have hdescent : baseEnd_2403647 < baseStart_2403647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403696 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_2403696 : Nat := 118140960795 + 2403696 * 2 ^ 59
def prefixEnd_2403696 : Nat := 4983230072969 + 3 ^ 40 * 2403696 * 2
def baseEnd_2403696 : Nat := 411417131763244254015203

theorem tailTrace_2403696 : CollatzResearch.WordTrace tailWord_2403696 prefixEnd_2403696 411417131763244254015203 := by
  unfold tailWord_2403696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43834997749913692719427471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58446663666551590292569961 43834997749913692719427471)
  ·
    refine ⟨65752496624870539079141207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43834997749913692719427471 65752496624870539079141207)
    ·
      refine ⟨98628744937305808618711811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65752496624870539079141207 98628744937305808618711811)
      ·
        refine ⟨147943117405958712928067717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98628744937305808618711811 147943117405958712928067717)
        ·
          refine ⟨27739334513617258674012697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147943117405958712928067717 27739334513617258674012697)
          ·
            refine ⟨20804500885212944005509523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27739334513617258674012697 20804500885212944005509523)
            ·
              refine ⟨31206751327819416008264285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20804500885212944005509523 31206751327819416008264285)
              ·
                refine ⟨11702531747932281003099107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31206751327819416008264285 11702531747932281003099107)
                ·
                  refine ⟨17553797621898421504648661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11702531747932281003099107 17553797621898421504648661)
                  ·
                    refine ⟨411417131763244254015203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17553797621898421504648661 411417131763244254015203)
                    ·
                      rfl

theorem cell23_2403696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_2403696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403696 prefixEnd_2403696 := by exact prefixLift 2403696
  have htrace : WordTrace (prefixWord ++ tailWord_2403696) baseStart_2403696 baseEnd_2403696 := by
    simpa [prefixWord, tailWord_2403696, baseEnd_2403696] using wordTrace_append hprefix tailTrace_2403696
  have hstable : (prefixWord ++ tailWord_2403696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403696).length < 2 ^ (prefixWord ++ tailWord_2403696).sum := by decide
  have hdescent : baseEnd_2403696 < baseStart_2403696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403706 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_2403706 : Nat := 118140960795 + 2403706 * 2 ^ 59
def prefixEnd_2403706 : Nat := 4983230072969 + 3 ^ 40 * 2403706 * 2
def baseEnd_2403706 : Nat := 1234256530096277722920563

theorem tailTrace_2403706 : CollatzResearch.WordTrace tailWord_2403706 prefixEnd_2403706 1234256530096277722920563 := by
  unfold tailWord_2403706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21917590057447789286679743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58446906819860771431145981 21917590057447789286679743)
  ·
    refine ⟨32876385086171683930019615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21917590057447789286679743 32876385086171683930019615)
    ·
      refine ⟨49314577629257525895029423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32876385086171683930019615 49314577629257525895029423)
      ·
        refine ⟨73971866443886288842544135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49314577629257525895029423 73971866443886288842544135)
        ·
          refine ⟨110957799665829433263816203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73971866443886288842544135 110957799665829433263816203)
          ·
            refine ⟨166436699498744149895724305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110957799665829433263816203 166436699498744149895724305)
            ·
              refine ⟨124827524624058112421793229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166436699498744149895724305 124827524624058112421793229)
              ·
                refine ⟨46810321734021792158172461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124827524624058112421793229 46810321734021792158172461)
                ·
                  refine ⟨17553870650258172059314673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46810321734021792158172461 17553870650258172059314673)
                  ·
                    refine ⟨13165402987693629044486005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17553870650258172059314673 13165402987693629044486005)
                    ·
                      refine ⟨1234256530096277722920563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13165402987693629044486005 1234256530096277722920563)
                      ·
                        rfl

theorem cell23_2403706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_2403706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403706 prefixEnd_2403706 := by exact prefixLift 2403706
  have htrace : WordTrace (prefixWord ++ tailWord_2403706) baseStart_2403706 baseEnd_2403706 := by
    simpa [prefixWord, tailWord_2403706, baseEnd_2403706] using wordTrace_append hprefix tailTrace_2403706
  have hstable : (prefixWord ++ tailWord_2403706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403706).length < 2 ^ (prefixWord ++ tailWord_2403706).sum := by decide
  have hdescent : baseEnd_2403706 < baseStart_2403706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403756 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 10]
def baseStart_2403756 : Nat := 118140960795 + 2403756 * 2 ^ 59
def prefixEnd_2403756 : Nat := 4983230072969 + 3 ^ 40 * 2403756 * 2
def baseEnd_2403756 : Nat := 137142467125444725255037

theorem tailTrace_2403756 : CollatzResearch.WordTrace tailWord_2403756 prefixEnd_2403756 137142467125444725255037 := by
  unfold tailWord_2403756
  simp only [CollatzResearch.WordTrace]
  refine ⟨43836091939805007843019561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58448122586406677124026081 43836091939805007843019561)
  ·
    refine ⟨32877068954853755882264671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43836091939805007843019561 32877068954853755882264671)
    ·
      refine ⟨49315603432280633823397007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32877068954853755882264671 49315603432280633823397007)
      ·
        refine ⟨73973405148420950735095511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49315603432280633823397007 73973405148420950735095511)
        ·
          refine ⟨110960107722631426102643267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73973405148420950735095511 110960107722631426102643267)
          ·
            refine ⟨166440161583947139153964901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110960107722631426102643267 166440161583947139153964901)
            ·
              refine ⟨31207530296990088591368419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166440161583947139153964901 31207530296990088591368419)
              ·
                refine ⟨46811295445485132887052629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31207530296990088591368419 46811295445485132887052629)
                ·
                  refine ⟨137142467125444725255037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46811295445485132887052629 137142467125444725255037)
                  ·
                    rfl

theorem cell23_2403756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_2403756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403756 prefixEnd_2403756 := by exact prefixLift 2403756
  have htrace : WordTrace (prefixWord ++ tailWord_2403756) baseStart_2403756 baseEnd_2403756 := by
    simpa [prefixWord, tailWord_2403756, baseEnd_2403756] using wordTrace_append hprefix tailTrace_2403756
  have hstable : (prefixWord ++ tailWord_2403756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403756).length < 2 ^ (prefixWord ++ tailWord_2403756).sum := by decide
  have hdescent : baseEnd_2403756 < baseStart_2403756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403800 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2403800 : Nat := 118140960795 + 2403800 * 2 ^ 59
def prefixEnd_2403800 : Nat := 4983230072969 + 3 ^ 40 * 2403800 * 2
def baseEnd_2403800 : Nat := 1234304797277800355145131

theorem tailTrace_2403800 : CollatzResearch.WordTrace tailWord_2403800 prefixEnd_2403800 1234304797277800355145131 := by
  unfold tailWord_2403800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43836894345725305600320427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58449192460967074133760569 43836894345725305600320427)
  ·
    refine ⟨65755341518587958400480641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43836894345725305600320427 65755341518587958400480641)
    ·
      refine ⟨49316506138940968800360481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65755341518587958400480641 49316506138940968800360481)
      ·
        refine ⟨36987379604205726600270361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49316506138940968800360481 36987379604205726600270361)
        ·
          refine ⟨27740534703154294950202771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36987379604205726600270361 27740534703154294950202771)
          ·
            refine ⟨41610802054731442425304157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27740534703154294950202771 41610802054731442425304157)
            ·
              refine ⟨15604050770524290909489059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41610802054731442425304157 15604050770524290909489059)
              ·
                refine ⟨23406076155786436364233589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15604050770524290909489059 23406076155786436364233589)
                ·
                  refine ⟨2194319639604978409146899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23406076155786436364233589 2194319639604978409146899)
                  ·
                    refine ⟨3291479459407467613720349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2194319639604978409146899 3291479459407467613720349)
                    ·
                      refine ⟨1234304797277800355145131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291479459407467613720349 1234304797277800355145131)
                      ·
                        rfl

theorem cell23_2403800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2403800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403800 prefixEnd_2403800 := by exact prefixLift 2403800
  have htrace : WordTrace (prefixWord ++ tailWord_2403800) baseStart_2403800 baseEnd_2403800 := by
    simpa [prefixWord, tailWord_2403800, baseEnd_2403800] using wordTrace_append hprefix tailTrace_2403800
  have hstable : (prefixWord ++ tailWord_2403800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403800).length < 2 ^ (prefixWord ++ tailWord_2403800).sum := by decide
  have hdescent : baseEnd_2403800 < baseStart_2403800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403843 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3]
def baseStart_2403843 : Nat := 118140960795 + 2403843 * 2 ^ 59
def prefixEnd_2403843 : Nat := 4983230072969 + 3 ^ 40 * 2403843 * 2
def baseEnd_2403843 : Nat := 1234326876945943686907433

theorem tailTrace_2403843 : CollatzResearch.WordTrace tailWord_2403843 prefixEnd_2403843 1234326876945943686907433 := by
  unfold tailWord_2403843
  simp only [CollatzResearch.WordTrace]
  refine ⟨87675357030294829544456183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58450238020196553029637455 87675357030294829544456183)
  ·
    refine ⟨131513035545442244316684275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87675357030294829544456183 131513035545442244316684275)
    ·
      refine ⟨197269553318163366475026413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131513035545442244316684275 197269553318163366475026413)
      ·
        refine ⟨73976082494311262428134905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197269553318163366475026413 73976082494311262428134905)
        ·
          refine ⟨55482061870733446821101179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73976082494311262428134905 55482061870733446821101179)
          ·
            refine ⟨83223092806100170231651769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55482061870733446821101179 83223092806100170231651769)
            ·
              refine ⟨62417319604575127673738827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83223092806100170231651769 62417319604575127673738827)
              ·
                refine ⟨93625979406862691510608241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62417319604575127673738827 93625979406862691510608241)
                ·
                  refine ⟨70219484555147018632956181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93625979406862691510608241 70219484555147018632956181)
                  ·
                    refine ⟨3291538338522516498419821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70219484555147018632956181 3291538338522516498419821)
                    ·
                      refine ⟨1234326876945943686907433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291538338522516498419821 1234326876945943686907433)
                      ·
                        rfl

theorem cell23_2403843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_2403843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403843 prefixEnd_2403843 := by exact prefixLift 2403843
  have htrace : WordTrace (prefixWord ++ tailWord_2403843) baseStart_2403843 baseEnd_2403843 := by
    simpa [prefixWord, tailWord_2403843, baseEnd_2403843] using wordTrace_append hprefix tailTrace_2403843
  have hstable : (prefixWord ++ tailWord_2403843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403843).length < 2 ^ (prefixWord ++ tailWord_2403843).sum := by decide
  have hdescent : baseEnd_2403843 < baseStart_2403843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403850 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_2403850 : Nat := 118140960795 + 2403850 * 2 ^ 59
def prefixEnd_2403850 : Nat := 4983230072969 + 3 ^ 40 * 2403850 * 2
def baseEnd_2403850 : Nat := 411443490436841719839967

theorem tailTrace_2403850 : CollatzResearch.WordTrace tailWord_2403850 prefixEnd_2403850 411443490436841719839967 := by
  unfold tailWord_2403850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21918903085317367434990251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58450408227512979826640669 21918903085317367434990251)
  ·
    refine ⟨32878354627976051152485377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21918903085317367434990251 32878354627976051152485377)
    ·
      refine ⟨24658765970982038364364033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32878354627976051152485377 24658765970982038364364033)
      ·
        refine ⟨18494074478236528773273025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24658765970982038364364033 18494074478236528773273025)
        ·
          refine ⟨13870555858677396579954769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18494074478236528773273025 13870555858677396579954769)
          ·
            refine ⟨10402916894008047434966077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13870555858677396579954769 10402916894008047434966077)
            ·
              refine ⟨3901093835253017788112279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10402916894008047434966077 3901093835253017788112279)
              ·
                refine ⟨5851640752879526682168419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901093835253017788112279 5851640752879526682168419)
                ·
                  refine ⟨8777461129319290023252629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851640752879526682168419 8777461129319290023252629)
                  ·
                    refine ⟨411443490436841719839967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8777461129319290023252629 411443490436841719839967)
                    ·
                      rfl

theorem cell23_2403850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_2403850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403850 prefixEnd_2403850 := by exact prefixLift 2403850
  have htrace : WordTrace (prefixWord ++ tailWord_2403850) baseStart_2403850 baseEnd_2403850 := by
    simpa [prefixWord, tailWord_2403850, baseEnd_2403850] using wordTrace_append hprefix tailTrace_2403850
  have hstable : (prefixWord ++ tailWord_2403850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403850).length < 2 ^ (prefixWord ++ tailWord_2403850).sum := by decide
  have hdescent : baseEnd_2403850 < baseStart_2403850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403857 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_2403857 : Nat := 118140960795 + 2403857 * 2 ^ 59
def prefixEnd_2403857 : Nat := 4983230072969 + 3 ^ 40 * 2403857 * 2
def baseEnd_2403857 : Nat := 1234334065675106632132369

theorem tailTrace_2403857 : CollatzResearch.WordTrace tailWord_2403857 prefixEnd_2403857 1234334065675106632132369 := by
  unfold tailWord_2403857
  simp only [CollatzResearch.WordTrace]
  refine ⟨87675867652244109935465825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58450578434829406623643883 87675867652244109935465825)
  ·
    refine ⟨65756900739183082451599369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87675867652244109935465825 65756900739183082451599369)
    ·
      refine ⟨49317675554387311838699527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65756900739183082451599369 49317675554387311838699527)
      ·
        refine ⟨73976513331580967758049291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49317675554387311838699527 73976513331580967758049291)
        ·
          refine ⟨110964769997371451637073937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73976513331580967758049291 110964769997371451637073937)
          ·
            refine ⟨83223577498028588727805453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110964769997371451637073937 83223577498028588727805453)
            ·
              refine ⟨31208841561760720772927045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83223577498028588727805453 31208841561760720772927045)
              ·
                refine ⟨5851657792830135144923821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31208841561760720772927045 5851657792830135144923821)
                ·
                  refine ⟨2194371672311300679346433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5851657792830135144923821 2194371672311300679346433)
                  ·
                    refine ⟨1645778754233475509509825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194371672311300679346433 1645778754233475509509825)
                    ·
                      refine ⟨1234334065675106632132369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645778754233475509509825 1234334065675106632132369)
                      ·
                        rfl

theorem cell23_2403857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_2403857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403857 prefixEnd_2403857 := by exact prefixLift 2403857
  have htrace : WordTrace (prefixWord ++ tailWord_2403857) baseStart_2403857 baseEnd_2403857 := by
    simpa [prefixWord, tailWord_2403857, baseEnd_2403857] using wordTrace_append hprefix tailTrace_2403857
  have hstable : (prefixWord ++ tailWord_2403857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403857).length < 2 ^ (prefixWord ++ tailWord_2403857).sum := by decide
  have hdescent : baseEnd_2403857 < baseStart_2403857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403901 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_2403901 : Nat := 118140960795 + 2403901 * 2 ^ 59
def prefixEnd_2403901 : Nat := 4983230072969 + 3 ^ 40 * 2403901 * 2
def baseEnd_2403901 : Nat := 411452219607968153327389

theorem tailTrace_2403901 : CollatzResearch.WordTrace tailWord_2403901 prefixEnd_2403901 411452219607968153327389 := by
  unfold tailWord_2403901
  simp only [CollatzResearch.WordTrace]
  refine ⟨87677472464084705450067557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58451648309389803633378371 87677472464084705450067557)
  ·
    refine ⟨16439526087015882271887667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87677472464084705450067557 16439526087015882271887667)
    ·
      refine ⟨24659289130523823407831501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16439526087015882271887667 24659289130523823407831501)
      ·
        refine ⟨9247233423946433777936813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24659289130523823407831501 9247233423946433777936813)
        ·
          refine ⟨3467712533979912666726305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9247233423946433777936813 3467712533979912666726305)
          ·
            refine ⟨2600784400484934500044729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3467712533979912666726305 2600784400484934500044729)
            ·
              refine ⟨1950588300363700875033547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600784400484934500044729 1950588300363700875033547)
              ·
                refine ⟨2925882450545551312550321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950588300363700875033547 2925882450545551312550321)
                ·
                  refine ⟨2194411837909163484412741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925882450545551312550321 2194411837909163484412741)
                  ·
                    refine ⟨411452219607968153327389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194411837909163484412741 411452219607968153327389)
                    ·
                      rfl

theorem cell23_2403901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_2403901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403901 prefixEnd_2403901 := by exact prefixLift 2403901
  have htrace : WordTrace (prefixWord ++ tailWord_2403901) baseStart_2403901 baseEnd_2403901 := by
    simpa [prefixWord, tailWord_2403901, baseEnd_2403901] using wordTrace_append hprefix tailTrace_2403901
  have hstable : (prefixWord ++ tailWord_2403901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403901).length < 2 ^ (prefixWord ++ tailWord_2403901).sum := by decide
  have hdescent : baseEnd_2403901 < baseStart_2403901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403911 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_2403911 : Nat := 118140960795 + 2403911 * 2 ^ 59
def prefixEnd_2403911 : Nat := 4983230072969 + 3 ^ 40 * 2403911 * 2
def baseEnd_2403911 : Nat := 1234361793630449420857121

theorem tailTrace_2403911 : CollatzResearch.WordTrace tailWord_2403911 prefixEnd_2403911 1234361793630449420857121 := by
  unfold tailWord_2403911
  simp only [CollatzResearch.WordTrace]
  refine ⟨87677837194048477157931587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58451891462698984771954391 87677837194048477157931587)
  ·
    refine ⟨131516755791072715736897381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87677837194048477157931587 131516755791072715736897381)
    ·
      refine ⟨24659391710826134200668259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131516755791072715736897381 24659391710826134200668259)
      ·
        refine ⟨36989087566239201301002389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24659391710826134200668259 36989087566239201301002389)
        ·
          refine ⟨1733863479667462560984487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36989087566239201301002389 1733863479667462560984487)
          ·
            refine ⟨2600795219501193841476731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733863479667462560984487 2600795219501193841476731)
            ·
              refine ⟨3901192829251790762215097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600795219501193841476731 3901192829251790762215097)
              ·
                refine ⟨2925894621938843071661323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901192829251790762215097 2925894621938843071661323)
                ·
                  refine ⟨4388841932908264607491985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925894621938843071661323 4388841932908264607491985)
                  ·
                    refine ⟨3291631449681198455618989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4388841932908264607491985 3291631449681198455618989)
                    ·
                      refine ⟨1234361793630449420857121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291631449681198455618989 1234361793630449420857121)
                      ·
                        rfl

theorem cell23_2403911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_2403911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403911 prefixEnd_2403911 := by exact prefixLift 2403911
  have htrace : WordTrace (prefixWord ++ tailWord_2403911) baseStart_2403911 baseEnd_2403911 := by
    simpa [prefixWord, tailWord_2403911, baseEnd_2403911] using wordTrace_append hprefix tailTrace_2403911
  have hstable : (prefixWord ++ tailWord_2403911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403911).length < 2 ^ (prefixWord ++ tailWord_2403911).sum := by decide
  have hdescent : baseEnd_2403911 < baseStart_2403911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403947 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 8, 2, 2]
def baseStart_2403947 : Nat := 118140960795 + 2403947 * 2 ^ 59
def prefixEnd_2403947 : Nat := 4983230072969 + 3 ^ 40 * 2403947 * 2
def baseEnd_2403947 : Nat := 1234380278934011280006955

theorem tailTrace_2403947 : CollatzResearch.WordTrace tailWord_2403947 prefixEnd_2403947 1234380278934011280006955 := by
  unfold tailWord_2403947
  simp only [CollatzResearch.WordTrace]
  refine ⟨87679150221918055306242095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58452766814612036870828063 87679150221918055306242095)
  ·
    refine ⟨131518725332877082959363143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87679150221918055306242095 131518725332877082959363143)
    ·
      refine ⟨197278087999315624439044715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131518725332877082959363143 197278087999315624439044715)
      ·
        refine ⟨295917131998973436658567073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197278087999315624439044715 295917131998973436658567073)
        ·
          refine ⟨221937848999230077493925305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295917131998973436658567073 221937848999230077493925305)
          ·
            refine ⟨166453386749422558120443979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221937848999230077493925305 166453386749422558120443979)
            ·
              refine ⟨249680080124133837180665969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166453386749422558120443979 249680080124133837180665969)
              ·
                refine ⟨187260060093100377885499477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249680080124133837180665969 187260060093100377885499477)
                ·
                  refine ⟨2194453829216020053345697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 187260060093100377885499477 2194453829216020053345697)
                  ·
                    refine ⟨1645840371912015040009273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194453829216020053345697 1645840371912015040009273)
                    ·
                      refine ⟨1234380278934011280006955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645840371912015040009273 1234380278934011280006955)
                      ·
                        rfl

theorem cell23_2403947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2, 2].length) (baseStart_2403947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403947 prefixEnd_2403947 := by exact prefixLift 2403947
  have htrace : WordTrace (prefixWord ++ tailWord_2403947) baseStart_2403947 baseEnd_2403947 := by
    simpa [prefixWord, tailWord_2403947, baseEnd_2403947] using wordTrace_append hprefix tailTrace_2403947
  have hstable : (prefixWord ++ tailWord_2403947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403947).length < 2 ^ (prefixWord ++ tailWord_2403947).sum := by decide
  have hdescent : baseEnd_2403947 < baseStart_2403947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403953 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 11]
def baseStart_2403953 : Nat := 118140960795 + 2403953 * 2 ^ 59
def prefixEnd_2403953 : Nat := 4983230072969 + 3 ^ 40 * 2403953 * 2
def baseEnd_2403953 : Nat := 137153706646437584059103

theorem tailTrace_2403953 : CollatzResearch.WordTrace tailWord_2403953 prefixEnd_2403953 137153706646437584059103 := by
  unfold tailWord_2403953
  simp only [CollatzResearch.WordTrace]
  refine ⟨87679369059896318330960513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58452912706597545553973675 87679369059896318330960513)
  ·
    refine ⟨65759526794922238748220385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87679369059896318330960513 65759526794922238748220385)
    ·
      refine ⟨49319645096191679061165289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65759526794922238748220385 49319645096191679061165289)
      ·
        refine ⟨36989733822143759295873967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49319645096191679061165289 36989733822143759295873967)
        ·
          refine ⟨55484600733215638943810951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36989733822143759295873967 55484600733215638943810951)
          ·
            refine ⟨83226901099823458415716427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55484600733215638943810951 83226901099823458415716427)
            ·
              refine ⟨124840351649735187623574641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83226901099823458415716427 124840351649735187623574641)
              ·
                refine ⟨93630263737301390717680981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124840351649735187623574641 93630263737301390717680981)
                ·
                  refine ⟨137153706646437584059103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 93630263737301390717680981 137153706646437584059103)
                  ·
                    rfl

theorem cell23_2403953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_2403953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403953 prefixEnd_2403953 := by exact prefixLift 2403953
  have htrace : WordTrace (prefixWord ++ tailWord_2403953) baseStart_2403953 baseEnd_2403953 := by
    simpa [prefixWord, tailWord_2403953, baseEnd_2403953] using wordTrace_append hprefix tailTrace_2403953
  have hstable : (prefixWord ++ tailWord_2403953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403953).length < 2 ^ (prefixWord ++ tailWord_2403953).sum := by decide
  have hdescent : baseEnd_2403953 < baseStart_2403953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403957 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2403957 : Nat := 118140960795 + 2403957 * 2 ^ 59
def prefixEnd_2403957 : Nat := 4983230072969 + 3 ^ 40 * 2403957 * 2
def baseEnd_2403957 : Nat := 411461804580185413627303

theorem tailTrace_2403957 : CollatzResearch.WordTrace tailWord_2403957 prefixEnd_2403957 411461804580185413627303 := by
  unfold tailWord_2403957
  simp only [CollatzResearch.WordTrace]
  refine ⟨87679514951881827014106125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58453009967921218009404083 87679514951881827014106125)
  ·
    refine ⟨32879818106955685130289797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87679514951881827014106125 32879818106955685130289797)
    ·
      refine ⟨6164965895054190961929337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32879818106955685130289797 6164965895054190961929337)
      ·
        refine ⟨4623724421290643221447003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6164965895054190961929337 4623724421290643221447003)
        ·
          refine ⟨6935586631935964832170505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623724421290643221447003 6935586631935964832170505)
          ·
            refine ⟨5201689973951973624127879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6935586631935964832170505 5201689973951973624127879)
            ·
              refine ⟨7802534960927960436191819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5201689973951973624127879 7802534960927960436191819)
              ·
                refine ⟨11703802441391940654287729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7802534960927960436191819 11703802441391940654287729)
                ·
                  refine ⟨8777851831043955490715797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11703802441391940654287729 8777851831043955490715797)
                  ·
                    refine ⟨411461804580185413627303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8777851831043955490715797 411461804580185413627303)
                    ·
                      rfl

theorem cell23_2403957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2403957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403957 prefixEnd_2403957 := by exact prefixLift 2403957
  have htrace : WordTrace (prefixWord ++ tailWord_2403957) baseStart_2403957 baseEnd_2403957 := by
    simpa [prefixWord, tailWord_2403957, baseEnd_2403957] using wordTrace_append hprefix tailTrace_2403957
  have hstable : (prefixWord ++ tailWord_2403957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403957).length < 2 ^ (prefixWord ++ tailWord_2403957).sum := by decide
  have hdescent : baseEnd_2403957 < baseStart_2403957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403980 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2403980 : Nat := 118140960795 + 2403980 * 2 ^ 59
def prefixEnd_2403980 : Nat := 4983230072969 + 3 ^ 40 * 2403980 * 2
def baseEnd_2403980 : Nat := 1234397223795609650894303

theorem tailTrace_2403980 : CollatzResearch.WordTrace tailWord_2403980 prefixEnd_2403980 1234397223795609650894303 := by
  unfold tailWord_2403980
  simp only [CollatzResearch.WordTrace]
  refine ⟨43840176915399250971096697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58453569220532334628128929 43840176915399250971096697)
  ·
    refine ⟨32880132686549438228322523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43840176915399250971096697 32880132686549438228322523)
    ·
      refine ⟨49320199029824157342483785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32880132686549438228322523 49320199029824157342483785)
      ·
        refine ⟨36990149272368118006862839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49320199029824157342483785 36990149272368118006862839)
        ·
          refine ⟨55485223908552177010294259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36990149272368118006862839 55485223908552177010294259)
          ·
            refine ⟨83227835862828265515441389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55485223908552177010294259 83227835862828265515441389)
            ·
              refine ⟨31210438448560599568290521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83227835862828265515441389 31210438448560599568290521)
              ·
                refine ⟨23407828836420449676217891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31210438448560599568290521 23407828836420449676217891)
                ·
                  refine ⟨35111743254630674514326837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23407828836420449676217891 35111743254630674514326837)
                  ·
                    refine ⟨3291725930121625735718141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35111743254630674514326837 3291725930121625735718141)
                    ·
                      refine ⟨1234397223795609650894303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291725930121625735718141 1234397223795609650894303)
                      ·
                        rfl

theorem cell23_2403980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2403980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403980 prefixEnd_2403980 := by exact prefixLift 2403980
  have htrace : WordTrace (prefixWord ++ tailWord_2403980) baseStart_2403980 baseEnd_2403980 := by
    simpa [prefixWord, tailWord_2403980, baseEnd_2403980] using wordTrace_append hprefix tailTrace_2403980
  have hstable : (prefixWord ++ tailWord_2403980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403980).length < 2 ^ (prefixWord ++ tailWord_2403980).sum := by decide
  have hdescent : baseEnd_2403980 < baseStart_2403980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2403998 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_2403998 : Nat := 118140960795 + 2403998 * 2 ^ 59
def prefixEnd_2403998 : Nat := 4983230072969 + 3 ^ 40 * 2403998 * 2
def baseEnd_2403998 : Nat := 1234406466447390580469221

theorem tailTrace_2403998 : CollatzResearch.WordTrace tailWord_2403998 prefixEnd_2403998 1234406466447390580469221 := by
  unfold tailWord_2403998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960126293091661377043581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58454006896488860677565765 10960126293091661377043581)
  ·
    refine ⟨4110047359909373016391343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10960126293091661377043581 4110047359909373016391343)
    ·
      refine ⟨6165071039864059524587015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110047359909373016391343 6165071039864059524587015)
      ·
        refine ⟨9247606559796089286880523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165071039864059524587015 9247606559796089286880523)
        ·
          refine ⟨13871409839694133930320785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9247606559796089286880523 13871409839694133930320785)
          ·
            refine ⟨10403557379770600447740589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13871409839694133930320785 10403557379770600447740589)
            ·
              refine ⟨3901334017413975167902721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10403557379770600447740589 3901334017413975167902721)
              ·
                refine ⟨2926000513060481375927041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901334017413975167902721 2926000513060481375927041)
                ·
                  refine ⟨2194500384795361031945281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926000513060481375927041 2194500384795361031945281)
                  ·
                    refine ⟨1645875288596520773958961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194500384795361031945281 1645875288596520773958961)
                    ·
                      refine ⟨1234406466447390580469221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645875288596520773958961 1234406466447390580469221)
                      ·
                        rfl

theorem cell23_2403998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_2403998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2403998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2403998 prefixEnd_2403998 := by exact prefixLift 2403998
  have htrace : WordTrace (prefixWord ++ tailWord_2403998) baseStart_2403998 baseEnd_2403998 := by
    simpa [prefixWord, tailWord_2403998, baseEnd_2403998] using wordTrace_append hprefix tailTrace_2403998
  have hstable : (prefixWord ++ tailWord_2403998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2403998).length < 2 ^ (prefixWord ++ tailWord_2403998).sum := by decide
  have hdescent : baseEnd_2403998 < baseStart_2403998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2403998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404038 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_2404038 : Nat := 118140960795 + 2404038 * 2 ^ 59
def prefixEnd_2404038 : Nat := 4983230072969 + 3 ^ 40 * 2404038 * 2
def baseEnd_2404038 : Nat := 137158556185952269329893

theorem tailTrace_2404038 : CollatzResearch.WordTrace tailWord_2404038 prefixEnd_2404038 137158556185952269329893 := by
  unfold tailWord_2404038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740077164518386807743899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58454979509725585231869845 2740077164518386807743899)
  ·
    refine ⟨4110115746777580211615849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740077164518386807743899 4110115746777580211615849)
    ·
      refine ⟨3082586810083185158711887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4110115746777580211615849 3082586810083185158711887)
      ·
        refine ⟨4623880215124777738067831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082586810083185158711887 4623880215124777738067831)
        ·
          refine ⟨6935820322687166607101747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623880215124777738067831 6935820322687166607101747)
          ·
            refine ⟨10403730484030749910652621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6935820322687166607101747 10403730484030749910652621)
            ·
              refine ⟨3901398931511531216494733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10403730484030749910652621 3901398931511531216494733)
              ·
                refine ⟨1463024599316824206185525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3901398931511531216494733 1463024599316824206185525)
                ·
                  refine ⟨137158556185952269329893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1463024599316824206185525 137158556185952269329893)
                  ·
                    rfl

theorem cell23_2404038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_2404038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404038 prefixEnd_2404038 := by exact prefixLift 2404038
  have htrace : WordTrace (prefixWord ++ tailWord_2404038) baseStart_2404038 baseEnd_2404038 := by
    simpa [prefixWord, tailWord_2404038, baseEnd_2404038] using wordTrace_append hprefix tailTrace_2404038
  have hstable : (prefixWord ++ tailWord_2404038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404038).length < 2 ^ (prefixWord ++ tailWord_2404038).sum := by decide
  have hdescent : baseEnd_2404038 < baseStart_2404038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404057 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_2404057 : Nat := 118140960795 + 2404057 * 2 ^ 59
def prefixEnd_2404057 : Nat := 4983230072969 + 3 ^ 40 * 2404057 * 2
def baseEnd_2404057 : Nat := 1234436761806005849631449

theorem tailTrace_2404057 : CollatzResearch.WordTrace tailWord_2404057 prefixEnd_2404057 1234436761806005849631449 := by
  unfold tailWord_2404057
  simp only [CollatzResearch.WordTrace]
  refine ⟨87683162251519544092746425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58455441501013029395164283 87683162251519544092746425)
  ·
    refine ⟨65762371688639658069559819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87683162251519544092746425 65762371688639658069559819)
    ·
      refine ⟨98643557532959487104339729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65762371688639658069559819 98643557532959487104339729)
      ·
        refine ⟨73982668149719615328254797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98643557532959487104339729 73982668149719615328254797)
        ·
          refine ⟨27743500556144855748095549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73982668149719615328254797 27743500556144855748095549)
          ·
            refine ⟨10403812708554320905535831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27743500556144855748095549 10403812708554320905535831)
            ·
              refine ⟨15605719062831481358303747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10403812708554320905535831 15605719062831481358303747)
              ·
                refine ⟨23408578594247222037455621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15605719062831481358303747 23408578594247222037455621)
                ·
                  refine ⟨4389108486421354132022929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23408578594247222037455621 4389108486421354132022929)
                  ·
                    refine ⟨3291831364816015599017197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4389108486421354132022929 3291831364816015599017197)
                    ·
                      refine ⟨1234436761806005849631449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3291831364816015599017197 1234436761806005849631449)
                      ·
                        rfl

theorem cell23_2404057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_2404057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404057 prefixEnd_2404057 := by exact prefixLift 2404057
  have htrace : WordTrace (prefixWord ++ tailWord_2404057) baseStart_2404057 baseEnd_2404057 := by
    simpa [prefixWord, tailWord_2404057, baseEnd_2404057] using wordTrace_append hprefix tailTrace_2404057
  have hstable : (prefixWord ++ tailWord_2404057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404057).length < 2 ^ (prefixWord ++ tailWord_2404057).sum := by decide
  have hdescent : baseEnd_2404057 < baseStart_2404057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404064 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 1, 4]
def baseStart_2404064 : Nat := 118140960795 + 2404064 * 2 ^ 59
def prefixEnd_2404064 : Nat := 4983230072969 + 3 ^ 40 * 2404064 * 2
def baseEnd_2404064 : Nat := 411480118723529107414639

theorem tailTrace_2404064 : CollatzResearch.WordTrace tailWord_2404064 prefixEnd_2404064 411480118723529107414639 := by
  unfold tailWord_2404064
  simp only [CollatzResearch.WordTrace]
  refine ⟨43841708781247092144125623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58455611708329456192167497 43841708781247092144125623)
  ·
    refine ⟨65762563171870638216188435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43841708781247092144125623 65762563171870638216188435)
    ·
      refine ⟨98643844757805957324282653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65762563171870638216188435 98643844757805957324282653)
      ·
        refine ⟨36991441784177233996605995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98643844757805957324282653 36991441784177233996605995)
        ·
          refine ⟨55487162676265850994908993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36991441784177233996605995 55487162676265850994908993)
          ·
            refine ⟨41615372007199388246181745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55487162676265850994908993 41615372007199388246181745)
            ·
              refine ⟨31211529005399541184636309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41615372007199388246181745 31211529005399541184636309)
              ·
                refine ⟨1463040422128103493029827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31211529005399541184636309 1463040422128103493029827)
                ·
                  refine ⟨2194560633192155239544741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463040422128103493029827 2194560633192155239544741)
                  ·
                    refine ⟨411480118723529107414639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194560633192155239544741 411480118723529107414639)
                    ·
                      rfl

theorem cell23_2404064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 4].length) (baseStart_2404064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404064 prefixEnd_2404064 := by exact prefixLift 2404064
  have htrace : WordTrace (prefixWord ++ tailWord_2404064) baseStart_2404064 baseEnd_2404064 := by
    simpa [prefixWord, tailWord_2404064, baseEnd_2404064] using wordTrace_append hprefix tailTrace_2404064
  have hstable : (prefixWord ++ tailWord_2404064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404064).length < 2 ^ (prefixWord ++ tailWord_2404064).sum := by decide
  have hdescent : baseEnd_2404064 < baseStart_2404064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404107 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 1, 5]
def baseStart_2404107 : Nat := 118140960795 + 2404107 * 2 ^ 59
def prefixEnd_2404107 : Nat := 4983230072969 + 3 ^ 40 * 2404107 * 2
def baseEnd_2404107 : Nat := 411487478612910218002073

theorem tailTrace_2404107 : CollatzResearch.WordTrace tailWord_2404107 prefixEnd_2404107 411487478612910218002073 := by
  unfold tailWord_2404107
  simp only [CollatzResearch.WordTrace]
  refine ⟨87684985901338402632066575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58456657267558935088044383 87684985901338402632066575)
  ·
    refine ⟨131527478852007603948099863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87684985901338402632066575 131527478852007603948099863)
    ·
      refine ⟨197291218278011405922149795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131527478852007603948099863 197291218278011405922149795)
      ·
        refine ⟨295936827417017108883224693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197291218278011405922149795 295936827417017108883224693)
        ·
          refine ⟨27744077570345353957802315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295936827417017108883224693 27744077570345353957802315)
          ·
            refine ⟨41616116355518030936703473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27744077570345353957802315 41616116355518030936703473)
            ·
              refine ⟨31212087266638523202527605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41616116355518030936703473 31212087266638523202527605)
              ·
                refine ⟨2926133181247361550236963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31212087266638523202527605 2926133181247361550236963)
                ·
                  refine ⟨4389199771871042325355445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926133181247361550236963 4389199771871042325355445)
                  ·
                    refine ⟨411487478612910218002073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4389199771871042325355445 411487478612910218002073)
                    ·
                      rfl

theorem cell23_2404107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 5].length) (baseStart_2404107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404107 prefixEnd_2404107 := by exact prefixLift 2404107
  have htrace : WordTrace (prefixWord ++ tailWord_2404107) baseStart_2404107 baseEnd_2404107 := by
    simpa [prefixWord, tailWord_2404107, baseEnd_2404107] using wordTrace_append hprefix tailTrace_2404107
  have hstable : (prefixWord ++ tailWord_2404107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404107).length < 2 ^ (prefixWord ++ tailWord_2404107).sum := by decide
  have hdescent : baseEnd_2404107 < baseStart_2404107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404127 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2404127 : Nat := 118140960795 + 2404127 * 2 ^ 59
def prefixEnd_2404127 : Nat := 4983230072969 + 3 ^ 40 * 2404127 * 2
def baseEnd_2404127 : Nat := 1234472705451820575756127

theorem tailTrace_2404127 : CollatzResearch.WordTrace tailWord_2404127 prefixEnd_2404127 1234472705451820575756127 := by
  unfold tailWord_2404127
  simp only [CollatzResearch.WordTrace]
  refine ⟨87685715361265946047794635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58457143574177297365196423 87685715361265946047794635)
  ·
    refine ⟨131528573041898919071691953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87685715361265946047794635 131528573041898919071691953)
    ·
      refine ⟨98646429781424189303768965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131528573041898919071691953 98646429781424189303768965)
      ·
        refine ⟨18496205584017035494456681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98646429781424189303768965 18496205584017035494456681)
        ·
          refine ⟨13872154188012776620842511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18496205584017035494456681 13872154188012776620842511)
          ·
            refine ⟨20808231282019164931263767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13872154188012776620842511 20808231282019164931263767)
            ·
              refine ⟨31212346923028747396895651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20808231282019164931263767 31212346923028747396895651)
              ·
                refine ⟨46818520384543121095343477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31212346923028747396895651 46818520384543121095343477)
                ·
                  refine ⟨4389236286050917602688451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46818520384543121095343477 4389236286050917602688451)
                  ·
                    refine ⟨6583854429076376404032677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4389236286050917602688451 6583854429076376404032677)
                    ·
                      refine ⟨1234472705451820575756127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6583854429076376404032677 1234472705451820575756127)
                      ·
                        rfl

theorem cell23_2404127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2404127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404127 prefixEnd_2404127 := by exact prefixLift 2404127
  have htrace : WordTrace (prefixWord ++ tailWord_2404127) baseStart_2404127 baseEnd_2404127 := by
    simpa [prefixWord, tailWord_2404127, baseEnd_2404127] using wordTrace_append hprefix tailTrace_2404127
  have hstable : (prefixWord ++ tailWord_2404127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404127).length < 2 ^ (prefixWord ++ tailWord_2404127).sum := by decide
  have hdescent : baseEnd_2404127 < baseStart_2404127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404148 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_2404148 : Nat := 118140960795 + 2404148 * 2 ^ 59
def prefixEnd_2404148 : Nat := 4983230072969 + 3 ^ 40 * 2404148 * 2
def baseEnd_2404148 : Nat := 1234483488545564993593531

theorem tailTrace_2404148 : CollatzResearch.WordTrace tailWord_2404148 prefixEnd_2404148 1234483488545564993593531 := by
  unfold tailWord_2404148
  simp only [CollatzResearch.WordTrace]
  refine ⟨43843240647094933317154549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58457654196126577756206065 43843240647094933317154549)
  ·
    refine ⟨4110303810665149998483239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43843240647094933317154549 4110303810665149998483239)
    ·
      refine ⟨6165455715997724997724859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110303810665149998483239 6165455715997724997724859)
      ·
        refine ⟨9248183573996587496587289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165455715997724997724859 9248183573996587496587289)
        ·
          refine ⟨6936137680497440622440467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248183573996587496587289 6936137680497440622440467)
          ·
            refine ⟨10404206520746160933660701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936137680497440622440467 10404206520746160933660701)
            ·
              refine ⟨3901577445279810350122763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10404206520746160933660701 3901577445279810350122763)
              ·
                refine ⟨5852366167919715525184145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901577445279810350122763 5852366167919715525184145)
                ·
                  refine ⟨4389274625939786643888109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5852366167919715525184145 4389274625939786643888109)
                  ·
                    refine ⟨1645977984727419991458041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4389274625939786643888109 1645977984727419991458041)
                    ·
                      refine ⟨1234483488545564993593531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645977984727419991458041 1234483488545564993593531)
                      ·
                        rfl

theorem cell23_2404148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_2404148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404148 prefixEnd_2404148 := by exact prefixLift 2404148
  have htrace : WordTrace (prefixWord ++ tailWord_2404148) baseStart_2404148 baseEnd_2404148 := by
    simpa [prefixWord, tailWord_2404148, baseEnd_2404148] using wordTrace_append hprefix tailTrace_2404148
  have hstable : (prefixWord ++ tailWord_2404148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404148).length < 2 ^ (prefixWord ++ tailWord_2404148).sum := by decide
  have hdescent : baseEnd_2404148 < baseStart_2404148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404158 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2404158 : Nat := 118140960795 + 2404158 * 2 ^ 59
def prefixEnd_2404158 : Nat := 4983230072969 + 3 ^ 40 * 2404158 * 2
def baseEnd_2404158 : Nat := 411496207784036651489495

theorem tailTrace_2404158 : CollatzResearch.WordTrace tailWord_2404158 prefixEnd_2404158 411496207784036651489495 := by
  unfold tailWord_2404158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960855753019204792771641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58457897349435758894782085 10960855753019204792771641)
  ·
    refine ⟨8220641814764403594578731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10960855753019204792771641 8220641814764403594578731)
    ·
      refine ⟨12330962722146605391868097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8220641814764403594578731 12330962722146605391868097)
      ·
        refine ⟨9248222041609954043901073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12330962722146605391868097 9248222041609954043901073)
        ·
          refine ⟨6936166531207465532925805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248222041609954043901073 6936166531207465532925805)
          ·
            refine ⟨2601062449202799574847177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6936166531207465532925805 2601062449202799574847177)
            ·
              refine ⟨1950796836902099681135383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601062449202799574847177 1950796836902099681135383)
              ·
                refine ⟨2926195255353149521703075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950796836902099681135383 2926195255353149521703075)
                ·
                  refine ⟨4389292883029724282554613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926195255353149521703075 4389292883029724282554613)
                  ·
                    refine ⟨411496207784036651489495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4389292883029724282554613 411496207784036651489495)
                    ·
                      rfl

theorem cell23_2404158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2404158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404158 prefixEnd_2404158 := by exact prefixLift 2404158
  have htrace : WordTrace (prefixWord ++ tailWord_2404158) baseStart_2404158 baseEnd_2404158 := by
    simpa [prefixWord, tailWord_2404158, baseEnd_2404158] using wordTrace_append hprefix tailTrace_2404158
  have hstable : (prefixWord ++ tailWord_2404158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404158).length < 2 ^ (prefixWord ++ tailWord_2404158).sum := by decide
  have hdescent : baseEnd_2404158 < baseStart_2404158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404178 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_2404178 : Nat := 118140960795 + 2404178 * 2 ^ 59
def prefixEnd_2404178 : Nat := 4983230072969 + 3 ^ 40 * 2404178 * 2
def baseEnd_2404178 : Nat := 1234498892965199876218393

theorem tailTrace_2404178 : CollatzResearch.WordTrace tailWord_2404178 prefixEnd_2404178 1234498892965199876218393 := by
  unfold tailWord_2404178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921893871020295439475297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58458383656054121171934125 21921893871020295439475297)
  ·
    refine ⟨16441420403265221579606473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21921893871020295439475297 16441420403265221579606473)
    ·
      refine ⟨12331065302448916184704855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16441420403265221579606473 12331065302448916184704855)
      ·
        refine ⟨18496597953673374277057283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12331065302448916184704855 18496597953673374277057283)
        ·
          refine ⟨27744896930510061415585925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18496597953673374277057283 27744896930510061415585925)
          ·
            refine ⟨5202168174470636515422361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27744896930510061415585925 5202168174470636515422361)
            ·
              refine ⟨3901626130852977386566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202168174470636515422361 3901626130852977386566771)
              ·
                refine ⟨5852439196279466079850157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901626130852977386566771 5852439196279466079850157)
                ·
                  refine ⟨2194664698604799779943809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5852439196279466079850157 2194664698604799779943809)
                  ·
                    refine ⟨1645998523953599834957857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194664698604799779943809 1645998523953599834957857)
                    ·
                      refine ⟨1234498892965199876218393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1645998523953599834957857 1234498892965199876218393)
                      ·
                        rfl

theorem cell23_2404178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_2404178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404178 prefixEnd_2404178 := by exact prefixLift 2404178
  have htrace : WordTrace (prefixWord ++ tailWord_2404178) baseStart_2404178 baseEnd_2404178 := by
    simpa [prefixWord, tailWord_2404178, baseEnd_2404178] using wordTrace_append hprefix tailTrace_2404178
  have hstable : (prefixWord ++ tailWord_2404178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404178).length < 2 ^ (prefixWord ++ tailWord_2404178).sum := by decide
  have hdescent : baseEnd_2404178 < baseStart_2404178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404188 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2404188 : Nat := 118140960795 + 2404188 * 2 ^ 59
def prefixEnd_2404188 : Nat := 4983230072969 + 3 ^ 40 * 2404188 * 2
def baseEnd_2404188 : Nat := 411501342590581612364449

theorem tailTrace_2404188 : CollatzResearch.WordTrace tailWord_2404188 prefixEnd_2404188 411501342590581612364449 := by
  unfold tailWord_2404188
  simp only [CollatzResearch.WordTrace]
  refine ⟨43843970107022476732882609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58458626809363302310510145 43843970107022476732882609)
  ·
    refine ⟨32882977580266857549661957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43843970107022476732882609 32882977580266857549661957)
    ·
      refine ⟨6165558296300035790561617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32882977580266857549661957 6165558296300035790561617)
      ·
        refine ⟨4624168722225026842921213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6165558296300035790561617 4624168722225026842921213)
        ·
          refine ⟨1734063270834385066095455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4624168722225026842921213 1734063270834385066095455)
          ·
            refine ⟨2601094906251577599143183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734063270834385066095455 2601094906251577599143183)
            ·
              refine ⟨3901642359377366398714775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601094906251577599143183 3901642359377366398714775)
              ·
                refine ⟨5852463539066049598072163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901642359377366398714775 5852463539066049598072163)
                ·
                  refine ⟨8778695308599074397108245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5852463539066049598072163 8778695308599074397108245)
                  ·
                    refine ⟨411501342590581612364449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8778695308599074397108245 411501342590581612364449)
                    ·
                      rfl

theorem cell23_2404188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2404188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404188 prefixEnd_2404188 := by exact prefixLift 2404188
  have htrace : WordTrace (prefixWord ++ tailWord_2404188) baseStart_2404188 baseEnd_2404188 := by
    simpa [prefixWord, tailWord_2404188, baseEnd_2404188] using wordTrace_append hprefix tailTrace_2404188
  have hstable : (prefixWord ++ tailWord_2404188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404188).length < 2 ^ (prefixWord ++ tailWord_2404188).sum := by decide
  have hdescent : baseEnd_2404188 < baseStart_2404188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404255 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2404255 : Nat := 118140960795 + 2404255 * 2 ^ 59
def prefixEnd_2404255 : Nat := 4983230072969 + 3 ^ 40 * 2404255 * 2
def baseEnd_2404255 : Nat := 1234538430975596074955539

theorem tailTrace_2404255 : CollatzResearch.WordTrace tailWord_2404255 prefixEnd_2404255 1234538430975596074955539 := by
  unfold tailWord_2404255
  simp only [CollatzResearch.WordTrace]
  refine ⟨87690383904802223908454219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58460255936534815938969479 87690383904802223908454219)
  ·
    refine ⟨131535575857203335862681329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87690383904802223908454219 131535575857203335862681329)
    ·
      refine ⟨98651681892902501897010997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131535575857203335862681329 98651681892902501897010997)
      ·
        refine ⟨9248595177459609552844781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98651681892902501897010997 9248595177459609552844781)
        ·
          refine ⟨3468223191547353582316793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9248595177459609552844781 3468223191547353582316793)
          ·
            refine ⟨2601167393660515186737595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3468223191547353582316793 2601167393660515186737595)
            ·
              refine ⟨3901751090490772780106393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601167393660515186737595 3901751090490772780106393)
              ·
                refine ⟨2926313317868079585079795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901751090490772780106393 2926313317868079585079795)
                ·
                  refine ⟨4389469976802119377619693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926313317868079585079795 4389469976802119377619693)
                  ·
                    refine ⟨1646051241300794766607385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4389469976802119377619693 1646051241300794766607385)
                    ·
                      refine ⟨1234538430975596074955539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646051241300794766607385 1234538430975596074955539)
                      ·
                        rfl

theorem cell23_2404255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2404255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404255 prefixEnd_2404255 := by exact prefixLift 2404255
  have htrace : WordTrace (prefixWord ++ tailWord_2404255) baseStart_2404255 baseEnd_2404255 := by
    simpa [prefixWord, tailWord_2404255, baseEnd_2404255] using wordTrace_append hprefix tailTrace_2404255
  have hstable : (prefixWord ++ tailWord_2404255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404255).length < 2 ^ (prefixWord ++ tailWord_2404255).sum := by decide
  have hdescent : baseEnd_2404255 < baseStart_2404255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404285 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_2404285 : Nat := 118140960795 + 2404285 * 2 ^ 59
def prefixEnd_2404285 : Nat := 4983230072969 + 3 ^ 40 * 2404285 * 2
def baseEnd_2404285 : Nat := 1234553835395230957580401

theorem tailTrace_2404285 : CollatzResearch.WordTrace tailWord_2404285 prefixEnd_2404285 1234553835395230957580401 := by
  unfold tailWord_2404285
  simp only [CollatzResearch.WordTrace]
  refine ⟨87691478094693539032046309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58460985396462359354697539 87691478094693539032046309)
  ·
    refine ⟨16442152142755038568508683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87691478094693539032046309 16442152142755038568508683)
    ·
      refine ⟨24663228214132557852763025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16442152142755038568508683 24663228214132557852763025)
      ·
        refine ⟨18497421160599418389572269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24663228214132557852763025 18497421160599418389572269)
        ·
          refine ⟨6936532935224781896089601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18497421160599418389572269 6936532935224781896089601)
          ·
            refine ⟨5202399701418586422067201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6936532935224781896089601 5202399701418586422067201)
            ·
              refine ⟨3901799776063939816550401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202399701418586422067201 3901799776063939816550401)
              ·
                refine ⟨2926349832047954862412801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901799776063939816550401 2926349832047954862412801)
                ·
                  refine ⟨2194762374035966146809601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926349832047954862412801 2194762374035966146809601)
                  ·
                    refine ⟨1646071780526974610107201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194762374035966146809601 1646071780526974610107201)
                    ·
                      refine ⟨1234553835395230957580401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646071780526974610107201 1234553835395230957580401)
                      ·
                        rfl

theorem cell23_2404285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_2404285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404285 prefixEnd_2404285 := by exact prefixLift 2404285
  have htrace : WordTrace (prefixWord ++ tailWord_2404285) baseStart_2404285 baseEnd_2404285 := by
    simpa [prefixWord, tailWord_2404285, baseEnd_2404285] using wordTrace_append hprefix tailTrace_2404285
  have hstable : (prefixWord ++ tailWord_2404285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404285).length < 2 ^ (prefixWord ++ tailWord_2404285).sum := by decide
  have hdescent : baseEnd_2404285 < baseStart_2404285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404324 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_2404324 : Nat := 118140960795 + 2404324 * 2 ^ 59
def prefixEnd_2404324 : Nat := 4983230072969 + 3 ^ 40 * 2404324 * 2
def baseEnd_2404324 : Nat := 1234573861140756304992721

theorem tailTrace_2404324 : CollatzResearch.WordTrace tailWord_2404324 prefixEnd_2404324 1234573861140756304992721 := by
  unfold tailWord_2404324
  simp only [CollatzResearch.WordTrace]
  refine ⟨43846450270776124346358013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58461933694368165795144017 43846450270776124346358013)
  ·
    refine ⟨16442418851541046629884255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43846450270776124346358013 16442418851541046629884255)
    ·
      refine ⟨24663628277311569944826383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16442418851541046629884255 24663628277311569944826383)
      ·
        refine ⟨36995442415967354917239575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24663628277311569944826383 36995442415967354917239575)
        ·
          refine ⟨55493163623951032375859363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36995442415967354917239575 55493163623951032375859363)
          ·
            refine ⟨83239745435926548563789045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55493163623951032375859363 83239745435926548563789045)
            ·
              refine ⟨7803726134618113927855223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83239745435926548563789045 7803726134618113927855223)
              ·
                refine ⟨11705589201927170891782835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803726134618113927855223 11705589201927170891782835)
                ·
                  refine ⟨17558383802890756337674253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11705589201927170891782835 17558383802890756337674253)
                  ·
                    refine ⟨6584393926084033626627845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17558383802890756337674253 6584393926084033626627845)
                    ·
                      refine ⟨1234573861140756304992721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6584393926084033626627845 1234573861140756304992721)
                      ·
                        rfl

theorem cell23_2404324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_2404324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404324 prefixEnd_2404324 := by exact prefixLift 2404324
  have htrace : WordTrace (prefixWord ++ tailWord_2404324) baseStart_2404324 baseEnd_2404324 := by
    simpa [prefixWord, tailWord_2404324, baseEnd_2404324] using wordTrace_append hprefix tailTrace_2404324
  have hstable : (prefixWord ++ tailWord_2404324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404324).length < 2 ^ (prefixWord ++ tailWord_2404324).sum := by decide
  have hdescent : baseEnd_2404324 < baseStart_2404324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404451 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2404451 : Nat := 118140960795 + 2404451 * 2 ^ 59
def prefixEnd_2404451 : Nat := 4983230072969 + 3 ^ 40 * 2404451 * 2
def baseEnd_2404451 : Nat := 1234639073183877308104637

theorem tailTrace_2404451 : CollatzResearch.WordTrace tailWord_2404451 prefixEnd_2404451 1234639073183877308104637 := by
  unfold tailWord_2404451
  simp only [CollatzResearch.WordTrace]
  refine ⟨87697532612092149382589207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58465021741394766255059471 87697532612092149382589207)
  ·
    refine ⟨131546298918138224073883811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87697532612092149382589207 131546298918138224073883811)
    ·
      refine ⟨197319448377207336110825717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131546298918138224073883811 197319448377207336110825717)
      ·
        refine ⟨18498698285363187760389911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197319448377207336110825717 18498698285363187760389911)
        ·
          refine ⟨27748047428044781640584867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18498698285363187760389911 27748047428044781640584867)
          ·
            refine ⟨41622071142067172460877301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27748047428044781640584867 41622071142067172460877301)
            ·
              refine ⟨3902069169568797418207247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41622071142067172460877301 3902069169568797418207247)
              ·
                refine ⟨5853103754353196127310871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902069169568797418207247 5853103754353196127310871)
                ·
                  refine ⟨8779655631529794190966307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853103754353196127310871 8779655631529794190966307)
                  ·
                    refine ⟨13169483447294691286449461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8779655631529794190966307 13169483447294691286449461)
                    ·
                      refine ⟨1234639073183877308104637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13169483447294691286449461 1234639073183877308104637)
                      ·
                        rfl

theorem cell23_2404451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2404451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404451 prefixEnd_2404451 := by exact prefixLift 2404451
  have htrace : WordTrace (prefixWord ++ tailWord_2404451) baseStart_2404451 baseEnd_2404451 := by
    simpa [prefixWord, tailWord_2404451, baseEnd_2404451] using wordTrace_append hprefix tailTrace_2404451
  have hstable : (prefixWord ++ tailWord_2404451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404451).length < 2 ^ (prefixWord ++ tailWord_2404451).sum := by decide
  have hdescent : baseEnd_2404451 < baseStart_2404451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404461 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2404461 : Nat := 118140960795 + 2404461 * 2 ^ 59
def prefixEnd_2404461 : Nat := 4983230072969 + 3 ^ 40 * 2404461 * 2
def baseEnd_2404461 : Nat := 1234644207990422268979591

theorem tailTrace_2404461 : CollatzResearch.WordTrace tailWord_2404461 prefixEnd_2404461 1234644207990422268979591 := by
  unfold tailWord_2404461
  simp only [CollatzResearch.WordTrace]
  refine ⟨87697897342055921090453237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58465264894703947393635491 87697897342055921090453237)
  ·
    refine ⟨8221677875817742602229991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87697897342055921090453237 8221677875817742602229991)
    ·
      refine ⟨12332516813726613903344987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8221677875817742602229991 12332516813726613903344987)
      ·
        refine ⟨18498775220589920855017481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332516813726613903344987 18498775220589920855017481)
        ·
          refine ⟨13874081415442440641263111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18498775220589920855017481 13874081415442440641263111)
          ·
            refine ⟨20811122123163660961894667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874081415442440641263111 20811122123163660961894667)
            ·
              refine ⟨31216683184745491442842001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20811122123163660961894667 31216683184745491442842001)
              ·
                refine ⟨23412512388559118582131501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31216683184745491442842001 23412512388559118582131501)
                ·
                  refine ⟨8779692145709669468299313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23412512388559118582131501 8779692145709669468299313)
                  ·
                    refine ⟨6584769109282252101224485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8779692145709669468299313 6584769109282252101224485)
                    ·
                      refine ⟨1234644207990422268979591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6584769109282252101224485 1234644207990422268979591)
                      ·
                        rfl

theorem cell23_2404461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2404461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404461 prefixEnd_2404461 := by exact prefixLift 2404461
  have htrace : WordTrace (prefixWord ++ tailWord_2404461) baseStart_2404461 baseEnd_2404461 := by
    simpa [prefixWord, tailWord_2404461, baseEnd_2404461] using wordTrace_append hprefix tailTrace_2404461
  have hstable : (prefixWord ++ tailWord_2404461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404461).length < 2 ^ (prefixWord ++ tailWord_2404461).sum := by decide
  have hdescent : baseEnd_2404461 < baseStart_2404461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404471 : List Nat := [1, 1, 3, 1, 1, 7, 1, 8]
def baseStart_2404471 : Nat := 118140960795 + 2404471 * 2 ^ 59
def prefixEnd_2404471 : Nat := 4983230072969 + 3 ^ 40 * 2404471 * 2
def baseEnd_2404471 : Nat := 45727753436924712216835

theorem tailTrace_2404471 : CollatzResearch.WordTrace tailWord_2404471 prefixEnd_2404471 45727753436924712216835 := by
  unfold tailWord_2404471
  simp only [CollatzResearch.WordTrace]
  refine ⟨87698262072019692798317267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58465508048013128532211511 87698262072019692798317267)
  ·
    refine ⟨131547393108029539197475901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87698262072019692798317267 131547393108029539197475901)
    ·
      refine ⟨49330272415511077199053463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131547393108029539197475901 49330272415511077199053463)
      ·
        refine ⟨73995408623266615798580195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49330272415511077199053463 73995408623266615798580195)
        ·
          refine ⟨110993112934899923697870293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73995408623266615798580195 110993112934899923697870293)
          ·
            refine ⟨2601401084411716961668835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110993112934899923697870293 2601401084411716961668835)
            ·
              refine ⟨3902101626617575442503253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601401084411716961668835 3902101626617575442503253)
              ·
                refine ⟨45727753436924712216835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3902101626617575442503253 45727753436924712216835)
                ·
                  rfl

theorem cell23_2404471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 8].length) (baseStart_2404471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404471 prefixEnd_2404471 := by exact prefixLift 2404471
  have htrace : WordTrace (prefixWord ++ tailWord_2404471) baseStart_2404471 baseEnd_2404471 := by
    simpa [prefixWord, tailWord_2404471, baseEnd_2404471] using wordTrace_append hprefix tailTrace_2404471
  have hstable : (prefixWord ++ tailWord_2404471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404471).length < 2 ^ (prefixWord ++ tailWord_2404471).sum := by decide
  have hdescent : baseEnd_2404471 < baseStart_2404471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404488 : List Nat := [2, 1, 3, 4, 1, 2, 3, 7]
def baseStart_2404488 : Nat := 118140960795 + 2404488 * 2 ^ 59
def prefixEnd_2404488 : Nat := 4983230072969 + 3 ^ 40 * 2404488 * 2
def baseEnd_2404488 : Nat := 45728076739559024568221

theorem tailTrace_2404488 : CollatzResearch.WordTrace tailWord_2404488 prefixEnd_2404488 45728076739559024568221 := by
  unfold tailWord_2404488
  simp only [CollatzResearch.WordTrace]
  refine ⟨43849441056479052350843059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58465921408638736467790745 43849441056479052350843059)
  ·
    refine ⟨65774161584718578526264589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43849441056479052350843059 65774161584718578526264589)
    ·
      refine ⟨24665310594269466947349221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65774161584718578526264589 24665310594269466947349221)
      ·
        refine ⟨4624745736425525052627979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24665310594269466947349221 4624745736425525052627979)
        ·
          refine ⟨6937118604638287578941969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624745736425525052627979 6937118604638287578941969)
          ·
            refine ⟨5202838953478715684206477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937118604638287578941969 5202838953478715684206477)
            ·
              refine ⟨1951064607554518381577429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5202838953478715684206477 1951064607554518381577429)
              ·
                refine ⟨45728076739559024568221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1951064607554518381577429 45728076739559024568221)
                ·
                  rfl

theorem cell23_2404488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 7].length) (baseStart_2404488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404488 prefixEnd_2404488 := by exact prefixLift 2404488
  have htrace : WordTrace (prefixWord ++ tailWord_2404488) baseStart_2404488 baseEnd_2404488 := by
    simpa [prefixWord, tailWord_2404488, baseEnd_2404488] using wordTrace_append hprefix tailTrace_2404488
  have hstable : (prefixWord ++ tailWord_2404488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404488).length < 2 ^ (prefixWord ++ tailWord_2404488).sum := by decide
  have hdescent : baseEnd_2404488 < baseStart_2404488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404498 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2404498 : Nat := 118140960795 + 2404498 * 2 ^ 59
def prefixEnd_2404498 : Nat := 4983230072969 + 3 ^ 40 * 2404498 * 2
def baseEnd_2404498 : Nat := 1234663206774638624216921

theorem tailTrace_2404498 : CollatzResearch.WordTrace tailWord_2404498 prefixEnd_2404498 1234663206774638624216921 := by
  unfold tailWord_2404498
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924811710730469102387537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58466164561947917606366765 21924811710730469102387537)
  ·
    refine ⟨16443608783047851826790653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21924811710730469102387537 16443608783047851826790653)
    ·
      refine ⟨6166353293642944435046495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16443608783047851826790653 6166353293642944435046495)
      ·
        refine ⟨9249529940464416652569743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166353293642944435046495 9249529940464416652569743)
        ·
          refine ⟨13874294910696624978854615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9249529940464416652569743 13874294910696624978854615)
          ·
            refine ⟨20811442366044937468281923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874294910696624978854615 20811442366044937468281923)
            ·
              refine ⟨31217163549067406202422885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20811442366044937468281923 31217163549067406202422885)
              ·
                refine ⟨5853218165450138662954291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31217163549067406202422885 5853218165450138662954291)
                ·
                  refine ⟨8779827248175207994431437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853218165450138662954291 8779827248175207994431437)
                  ·
                    refine ⟨3292435218065702997911789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8779827248175207994431437 3292435218065702997911789)
                    ·
                      refine ⟨1234663206774638624216921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292435218065702997911789 1234663206774638624216921)
                      ·
                        rfl

theorem cell23_2404498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2404498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404498 prefixEnd_2404498 := by exact prefixLift 2404498
  have htrace : WordTrace (prefixWord ++ tailWord_2404498) baseStart_2404498 baseEnd_2404498 := by
    simpa [prefixWord, tailWord_2404498, baseEnd_2404498] using wordTrace_append hprefix tailTrace_2404498
  have hstable : (prefixWord ++ tailWord_2404498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404498).length < 2 ^ (prefixWord ++ tailWord_2404498).sum := by decide
  have hdescent : baseEnd_2404498 < baseStart_2404498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404541 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2404541 : Nat := 118140960795 + 2404541 * 2 ^ 59
def prefixEnd_2404541 : Nat := 4983230072969 + 3 ^ 40 * 2404541 * 2
def baseEnd_2404541 : Nat := 1234685286442781955979223

theorem tailTrace_2404541 : CollatzResearch.WordTrace tailWord_2404541 prefixEnd_2404541 1234685286442781955979223 := by
  unfold tailWord_2404541
  simp only [CollatzResearch.WordTrace]
  refine ⟨87700815181766094753365477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58467210121177396502243651 87700815181766094753365477)
  ·
    refine ⟨16443902846581142766256027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87700815181766094753365477 16443902846581142766256027)
    ·
      refine ⟨24665854269871714149384041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16443902846581142766256027 24665854269871714149384041)
      ·
        refine ⟨18499390702403785612038031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24665854269871714149384041 18499390702403785612038031)
        ·
          refine ⟨27749086053605678418057047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499390702403785612038031 27749086053605678418057047)
          ·
            refine ⟨41623629080408517627085571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27749086053605678418057047 41623629080408517627085571)
            ·
              refine ⟨62435443620612776440628357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41623629080408517627085571 62435443620612776440628357)
              ·
                refine ⟨11706645678864895582617817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62435443620612776440628357 11706645678864895582617817)
                ·
                  refine ⟨8779984259148671686963363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11706645678864895582617817 8779984259148671686963363)
                  ·
                    refine ⟨13169976388723007530445045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8779984259148671686963363 13169976388723007530445045)
                    ·
                      refine ⟨1234685286442781955979223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13169976388723007530445045 1234685286442781955979223)
                      ·
                        rfl

theorem cell23_2404541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2404541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404541 prefixEnd_2404541 := by exact prefixLift 2404541
  have htrace : WordTrace (prefixWord ++ tailWord_2404541) baseStart_2404541 baseEnd_2404541 := by
    simpa [prefixWord, tailWord_2404541, baseEnd_2404541] using wordTrace_append hprefix tailTrace_2404541
  have hstable : (prefixWord ++ tailWord_2404541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404541).length < 2 ^ (prefixWord ++ tailWord_2404541).sum := by decide
  have hdescent : baseEnd_2404541 < baseStart_2404541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404558 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2404558 : Nat := 118140960795 + 2404558 * 2 ^ 59
def prefixEnd_2404558 : Nat := 4983230072969 + 3 ^ 40 * 2404558 * 2
def baseEnd_2404558 : Nat := 1234694015613908389466645

theorem tailTrace_2404558 : CollatzResearch.WordTrace tailWord_2404558 prefixEnd_2404558 1234694015613908389466645 := by
  unfold tailWord_2404558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962679402838063332091791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58467623481803004437822885 10962679402838063332091791)
  ·
    refine ⟨16444019104257094998137687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10962679402838063332091791 16444019104257094998137687)
    ·
      refine ⟨24666028656385642497206531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16444019104257094998137687 24666028656385642497206531)
      ·
        refine ⟨36999042984578463745809797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24666028656385642497206531 36999042984578463745809797)
        ·
          refine ⟨6937320559608461952339337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36999042984578463745809797 6937320559608461952339337)
          ·
            refine ⟨5202990419706346464254503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937320559608461952339337 5202990419706346464254503)
            ·
              refine ⟨7804485629559519696381755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202990419706346464254503 7804485629559519696381755)
              ·
                refine ⟨11706728444339279544572633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804485629559519696381755 11706728444339279544572633)
                ·
                  refine ⟨8780046333254459658429475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11706728444339279544572633 8780046333254459658429475)
                  ·
                    refine ⟨13170069499881689487644213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8780046333254459658429475 13170069499881689487644213)
                    ·
                      refine ⟨1234694015613908389466645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13170069499881689487644213 1234694015613908389466645)
                      ·
                        rfl

theorem cell23_2404558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2404558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404558 prefixEnd_2404558 := by exact prefixLift 2404558
  have htrace : WordTrace (prefixWord ++ tailWord_2404558) baseStart_2404558 baseEnd_2404558 := by
    simpa [prefixWord, tailWord_2404558, baseEnd_2404558] using wordTrace_append hprefix tailTrace_2404558
  have hstable : (prefixWord ++ tailWord_2404558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404558).length < 2 ^ (prefixWord ++ tailWord_2404558).sum := by decide
  have hdescent : baseEnd_2404558 < baseStart_2404558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404589 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2404589 : Nat := 118140960795 + 2404589 * 2 ^ 59
def prefixEnd_2404589 : Nat := 4983230072969 + 3 ^ 40 * 2404589 * 2
def baseEnd_2404589 : Nat := 1234709933514197768179003

theorem tailTrace_2404589 : CollatzResearch.WordTrace tailWord_2404589 prefixEnd_2404589 1234709933514197768179003 := by
  unfold tailWord_2404589
  simp only [CollatzResearch.WordTrace]
  refine ⟨87702565885592198951112821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58468377257061465967408547 87702565885592198951112821)
  ·
    refine ⟨8222115551774268651666827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87702565885592198951112821 8222115551774268651666827)
    ·
      refine ⟨12333173327661402977500241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8222115551774268651666827 12333173327661402977500241)
      ·
        refine ⟨9249879995746052233125181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12333173327661402977500241 9249879995746052233125181)
        ·
          refine ⟨3468704998404769587421943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9249879995746052233125181 3468704998404769587421943)
          ·
            refine ⟨5203057497607154381132915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468704998404769587421943 5203057497607154381132915)
            ·
              refine ⟨7804586246410731571699373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203057497607154381132915 7804586246410731571699373)
              ·
                refine ⟨2926719842404024339387265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7804586246410731571699373 2926719842404024339387265)
                ·
                  refine ⟨2195039881803018254540449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926719842404024339387265 2195039881803018254540449)
                  ·
                    refine ⟨1646279911352263690905337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195039881803018254540449 1646279911352263690905337)
                    ·
                      refine ⟨1234709933514197768179003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646279911352263690905337 1234709933514197768179003)
                      ·
                        rfl

theorem cell23_2404589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2404589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404589 prefixEnd_2404589 := by exact prefixLift 2404589
  have htrace : WordTrace (prefixWord ++ tailWord_2404589) baseStart_2404589 baseEnd_2404589 := by
    simpa [prefixWord, tailWord_2404589, baseEnd_2404589] using wordTrace_append hprefix tailTrace_2404589
  have hstable : (prefixWord ++ tailWord_2404589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404589).length < 2 ^ (prefixWord ++ tailWord_2404589).sum := by decide
  have hdescent : baseEnd_2404589 < baseStart_2404589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404665 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2404665 : Nat := 118140960795 + 2404665 * 2 ^ 59
def prefixEnd_2404665 : Nat := 4983230072969 + 3 ^ 40 * 2404665 * 2
def baseEnd_2404665 : Nat := 1234748958043939470828653

theorem tailTrace_2404665 : CollatzResearch.WordTrace tailWord_2404665 prefixEnd_2404665 1234748958043939470828653 := by
  unfold tailWord_2404665
  simp only [CollatzResearch.WordTrace]
  refine ⟨87705337833316863930879449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58470225222211242620586299 87705337833316863930879449)
  ·
    refine ⟨65779003374987647948159587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87705337833316863930879449 65779003374987647948159587)
    ·
      refine ⟨98668505062481471922239381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65779003374987647948159587 98668505062481471922239381)
      ·
        refine ⟨4625086174803818996354971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98668505062481471922239381 4625086174803818996354971)
        ·
          refine ⟨6937629262205728494532457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4625086174803818996354971 6937629262205728494532457)
          ·
            refine ⟨5203221946654296370899343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937629262205728494532457 5203221946654296370899343)
            ·
              refine ⟨7804832919981444556349015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203221946654296370899343 7804832919981444556349015)
              ·
                refine ⟨11707249379972166834523523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804832919981444556349015 11707249379972166834523523)
                ·
                  refine ⟨17560874069958250251785285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11707249379972166834523523 17560874069958250251785285)
                  ·
                    refine ⟨3292663888117171922209741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17560874069958250251785285 3292663888117171922209741)
                    ·
                      refine ⟨1234748958043939470828653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292663888117171922209741 1234748958043939470828653)
                      ·
                        rfl

theorem cell23_2404665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2404665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404665 prefixEnd_2404665 := by exact prefixLift 2404665
  have htrace : WordTrace (prefixWord ++ tailWord_2404665) baseStart_2404665 baseEnd_2404665 := by
    simpa [prefixWord, tailWord_2404665, baseEnd_2404665] using wordTrace_append hprefix tailTrace_2404665
  have hstable : (prefixWord ++ tailWord_2404665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404665).length < 2 ^ (prefixWord ++ tailWord_2404665).sum := by decide
  have hdescent : baseEnd_2404665 < baseStart_2404665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404691 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_2404691 : Nat := 118140960795 + 2404691 * 2 ^ 59
def prefixEnd_2404691 : Nat := 4983230072969 + 3 ^ 40 * 2404691 * 2
def baseEnd_2404691 : Nat := 1234762308540956369103533

theorem tailTrace_2404691 : CollatzResearch.WordTrace tailWord_2404691 prefixEnd_2404691 1234762308540956369103533 := by
  unfold tailWord_2404691
  simp only [CollatzResearch.WordTrace]
  refine ⟨87706286131222670371325927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58470857420815113580883951 87706286131222670371325927)
  ·
    refine ⟨131559429196834005556988891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87706286131222670371325927 131559429196834005556988891)
    ·
      refine ⟨197339143795251008335483337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131559429196834005556988891 197339143795251008335483337)
      ·
        refine ⟨148004357846438256251612503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197339143795251008335483337 148004357846438256251612503)
        ·
          refine ⟨222006536769657384377418755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148004357846438256251612503 222006536769657384377418755)
          ·
            refine ⟨333009805154486076566128133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222006536769657384377418755 333009805154486076566128133)
            ·
              refine ⟨62439338466466139356149025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333009805154486076566128133 62439338466466139356149025)
              ·
                refine ⟨46829503849849604517111769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62439338466466139356149025 46829503849849604517111769)
                ·
                  refine ⟨35122127887387203387833827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46829503849849604517111769 35122127887387203387833827)
                  ·
                    refine ⟨52683191831080805081750741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35122127887387203387833827 52683191831080805081750741)
                    ·
                      refine ⟨1234762308540956369103533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52683191831080805081750741 1234762308540956369103533)
                      ·
                        rfl

theorem cell23_2404691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_2404691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404691 prefixEnd_2404691 := by exact prefixLift 2404691
  have htrace : WordTrace (prefixWord ++ tailWord_2404691) baseStart_2404691 baseEnd_2404691 := by
    simpa [prefixWord, tailWord_2404691, baseEnd_2404691] using wordTrace_append hprefix tailTrace_2404691
  have hstable : (prefixWord ++ tailWord_2404691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404691).length < 2 ^ (prefixWord ++ tailWord_2404691).sum := by decide
  have hdescent : baseEnd_2404691 < baseStart_2404691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404712 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2404712 : Nat := 118140960795 + 2404712 * 2 ^ 59
def prefixEnd_2404712 : Nat := 4983230072969 + 3 ^ 40 * 2404712 * 2
def baseEnd_2404712 : Nat := 1234773091634700786940937

theorem tailTrace_2404712 : CollatzResearch.WordTrace tailWord_2404712 prefixEnd_2404712 1234773091634700786940937 := by
  unfold tailWord_2404712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43853526032073295478920195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58471368042764393971893593 43853526032073295478920195)
  ·
    refine ⟨65780289048109943218380293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43853526032073295478920195 65780289048109943218380293)
    ·
      refine ⟨12333804196520614353446305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65780289048109943218380293 12333804196520614353446305)
      ·
        refine ⟨9250353147390460765084729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12333804196520614353446305 9250353147390460765084729)
        ·
          refine ⟨6937764860542845573813547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9250353147390460765084729 6937764860542845573813547)
          ·
            refine ⟨10406647290814268360720321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937764860542845573813547 10406647290814268360720321)
            ·
              refine ⟨7804985468110701270540241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10406647290814268360720321 7804985468110701270540241)
              ·
                refine ⟨5853739101083025952905181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7804985468110701270540241 5853739101083025952905181)
                ·
                  refine ⟨2195152162906134732339443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5853739101083025952905181 2195152162906134732339443)
                  ·
                    refine ⟨3292728244359202098509165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195152162906134732339443 3292728244359202098509165)
                    ·
                      refine ⟨1234773091634700786940937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292728244359202098509165 1234773091634700786940937)
                      ·
                        rfl

theorem cell23_2404712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2404712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404712 prefixEnd_2404712 := by exact prefixLift 2404712
  have htrace : WordTrace (prefixWord ++ tailWord_2404712) baseStart_2404712 baseEnd_2404712 := by
    simpa [prefixWord, tailWord_2404712, baseEnd_2404712] using wordTrace_append hprefix tailTrace_2404712
  have hstable : (prefixWord ++ tailWord_2404712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404712).length < 2 ^ (prefixWord ++ tailWord_2404712).sum := by decide
  have hdescent : baseEnd_2404712 < baseStart_2404712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404745 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_2404745 : Nat := 118140960795 + 2404745 * 2 ^ 59
def prefixEnd_2404745 : Nat := 4983230072969 + 3 ^ 40 * 2404745 * 2
def baseEnd_2404745 : Nat := 411596678832099719276095

theorem tailTrace_2404745 : CollatzResearch.WordTrace tailWord_2404745 prefixEnd_2404745 411596678832099719276095 := by
  unfold tailWord_2404745
  simp only [CollatzResearch.WordTrace]
  refine ⟨87708255673027037593791689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58472170448684691729194459 87708255673027037593791689)
  ·
    refine ⟨65781191754770278195343767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87708255673027037593791689 65781191754770278195343767)
    ·
      refine ⟨98671787632155417293015651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65781191754770278195343767 98671787632155417293015651)
      ·
        refine ⟨148007681448233125939523477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98671787632155417293015651 148007681448233125939523477)
        ·
          refine ⟨6937860067885927778415163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148007681448233125939523477 6937860067885927778415163)
          ·
            refine ⟨10406790101828891667622745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937860067885927778415163 10406790101828891667622745)
            ·
              refine ⟨7805092576371668750717059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10406790101828891667622745 7805092576371668750717059)
              ·
                refine ⟨11707638864557503126075589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7805092576371668750717059 11707638864557503126075589)
                ·
                  refine ⟨2195182287104531836139173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11707638864557503126075589 2195182287104531836139173)
                  ·
                    refine ⟨411596678832099719276095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195182287104531836139173 411596678832099719276095)
                    ·
                      rfl

theorem cell23_2404745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_2404745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404745 prefixEnd_2404745 := by exact prefixLift 2404745
  have htrace : WordTrace (prefixWord ++ tailWord_2404745) baseStart_2404745 baseEnd_2404745 := by
    simpa [prefixWord, tailWord_2404745, baseEnd_2404745] using wordTrace_append hprefix tailTrace_2404745
  have hstable : (prefixWord ++ tailWord_2404745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404745).length < 2 ^ (prefixWord ++ tailWord_2404745).sum := by decide
  have hdescent : baseEnd_2404745 < baseStart_2404745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404746 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2404746 : Nat := 118140960795 + 2404746 * 2 ^ 59
def prefixEnd_2404746 : Nat := 4983230072969 + 3 ^ 40 * 2404746 * 2
def baseEnd_2404746 : Nat := 1234790549976953653915781

theorem tailTrace_2404746 : CollatzResearch.WordTrace tailWord_2404746 prefixEnd_2404746 1234790549976953653915781 := by
  unfold tailWord_2404746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21927073036505853691144523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58472194764015609843052061 21927073036505853691144523)
  ·
    refine ⟨32890609554758780536716785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21927073036505853691144523 32890609554758780536716785)
    ·
      refine ⟨24667957166069085402537589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32890609554758780536716785 24667957166069085402537589)
      ·
        refine ⟨2312620984318976756487899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24667957166069085402537589 2312620984318976756487899)
        ·
          refine ⟨3468931476478465134731849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312620984318976756487899 3468931476478465134731849)
          ·
            refine ⟨2601698607358848851048887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3468931476478465134731849 2601698607358848851048887)
            ·
              refine ⟨3902547911038273276573331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601698607358848851048887 3902547911038273276573331)
              ·
                refine ⟨5853821866557409914859997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902547911038273276573331 5853821866557409914859997)
                ·
                  refine ⟨2195183199959028718072499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5853821866557409914859997 2195183199959028718072499)
                  ·
                    refine ⟨3292774799938543077108749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195183199959028718072499 3292774799938543077108749)
                    ·
                      refine ⟨1234790549976953653915781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292774799938543077108749 1234790549976953653915781)
                      ·
                        rfl

theorem cell23_2404746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2404746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404746 prefixEnd_2404746 := by exact prefixLift 2404746
  have htrace : WordTrace (prefixWord ++ tailWord_2404746) baseStart_2404746 baseEnd_2404746 := by
    simpa [prefixWord, tailWord_2404746, baseEnd_2404746] using wordTrace_append hprefix tailTrace_2404746
  have hstable : (prefixWord ++ tailWord_2404746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404746).length < 2 ^ (prefixWord ++ tailWord_2404746).sum := by decide
  have hdescent : baseEnd_2404746 < baseStart_2404746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404748 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2404748 : Nat := 118140960795 + 2404748 * 2 ^ 59
def prefixEnd_2404748 : Nat := 4983230072969 + 3 ^ 40 * 2404748 * 2
def baseEnd_2404748 : Nat := 1234791576938262646090771

theorem tailTrace_2404748 : CollatzResearch.WordTrace tailWord_2404748 prefixEnd_2404748 1234791576938262646090771 := by
  unfold tailWord_2404748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43854182546008084553075449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58472243394677446070767265 43854182546008084553075449)
  ·
    refine ⟨32890636909506063414806587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43854182546008084553075449 32890636909506063414806587)
    ·
      refine ⟨49335955364259095122209881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32890636909506063414806587 49335955364259095122209881)
      ·
        refine ⟨37001966523194321341657411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49335955364259095122209881 37001966523194321341657411)
        ·
          refine ⟨55502949784791482012486117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37001966523194321341657411 55502949784791482012486117)
          ·
            refine ⟨10406803084648402877341147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55502949784791482012486117 10406803084648402877341147)
            ·
              refine ⟨15610204626972604316011721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10406803084648402877341147 15610204626972604316011721)
              ·
                refine ⟨11707653470229453237008791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15610204626972604316011721 11707653470229453237008791)
                ·
                  refine ⟨17561480205344179855513187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11707653470229453237008791 17561480205344179855513187)
                  ·
                    refine ⟨26342220308016269783269781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17561480205344179855513187 26342220308016269783269781)
                    ·
                      refine ⟨1234791576938262646090771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26342220308016269783269781 1234791576938262646090771)
                      ·
                        rfl

theorem cell23_2404748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2404748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404748 prefixEnd_2404748 := by exact prefixLift 2404748
  have htrace : WordTrace (prefixWord ++ tailWord_2404748) baseStart_2404748 baseEnd_2404748 := by
    simpa [prefixWord, tailWord_2404748, baseEnd_2404748] using wordTrace_append hprefix tailTrace_2404748
  have hstable : (prefixWord ++ tailWord_2404748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404748).length < 2 ^ (prefixWord ++ tailWord_2404748).sum := by decide
  have hdescent : baseEnd_2404748 < baseStart_2404748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404762 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_2404762 : Nat := 118140960795 + 2404762 * 2 ^ 59
def prefixEnd_2404762 : Nat := 4983230072969 + 3 ^ 40 * 2404762 * 2
def baseEnd_2404762 : Nat := 411599588555808530438569

theorem tailTrace_2404762 : CollatzResearch.WordTrace tailWord_2404762 prefixEnd_2404762 411599588555808530438569 := by
  unfold tailWord_2404762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21927218928491362374290135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58472583809310299664773693 21927218928491362374290135)
  ·
    refine ⟨32890828392737043561435203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21927218928491362374290135 32890828392737043561435203)
    ·
      refine ⟨49336242589105565342152805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32890828392737043561435203 49336242589105565342152805)
      ·
        refine ⟨9250545485457293501653651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49336242589105565342152805 9250545485457293501653651)
        ·
          refine ⟨13875818228185940252480477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9250545485457293501653651 13875818228185940252480477)
          ·
            refine ⟨5203431835569727594680179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13875818228185940252480477 5203431835569727594680179)
            ·
              refine ⟨7805147753354591392020269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203431835569727594680179 7805147753354591392020269)
              ·
                refine ⟨2926930407507971772007601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7805147753354591392020269 2926930407507971772007601)
                ·
                  refine ⟨2195197805630978829005701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926930407507971772007601 2195197805630978829005701)
                  ·
                    refine ⟨411599588555808530438569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195197805630978829005701 411599588555808530438569)
                    ·
                      rfl

theorem cell23_2404762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_2404762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404762 prefixEnd_2404762 := by exact prefixLift 2404762
  have htrace : WordTrace (prefixWord ++ tailWord_2404762) baseStart_2404762 baseEnd_2404762 := by
    simpa [prefixWord, tailWord_2404762, baseEnd_2404762] using wordTrace_append hprefix tailTrace_2404762
  have hstable : (prefixWord ++ tailWord_2404762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404762).length < 2 ^ (prefixWord ++ tailWord_2404762).sum := by decide
  have hdescent : baseEnd_2404762 < baseStart_2404762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404772 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_2404772 : Nat := 118140960795 + 2404772 * 2 ^ 59
def prefixEnd_2404772 : Nat := 4983230072969 + 3 ^ 40 * 2404772 * 2
def baseEnd_2404772 : Nat := 1234803900473970552190661

theorem tailTrace_2404772 : CollatzResearch.WordTrace tailWord_2404772 prefixEnd_2404772 1234803900473970552190661 := by
  unfold tailWord_2404772
  simp only [CollatzResearch.WordTrace]
  refine ⟨43854620221964610602512285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58472826962619480803349713 43854620221964610602512285)
  ·
    refine ⟨16445482583236728975942107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43854620221964610602512285 16445482583236728975942107)
    ·
      refine ⟨24668223874855093463913161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445482583236728975942107 24668223874855093463913161)
      ·
        refine ⟨18501167906141320097934871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24668223874855093463913161 18501167906141320097934871)
        ·
          refine ⟨27751751859211980146902307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18501167906141320097934871 27751751859211980146902307)
          ·
            refine ⟨41627627788817970220353461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27751751859211980146902307 41627627788817970220353461)
            ·
              refine ⟨3902590105201684708158137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41627627788817970220353461 3902590105201684708158137)
              ·
                refine ⟨2926942578901263531118603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3902590105201684708158137 2926942578901263531118603)
                ·
                  refine ⟨4390413868351895296677905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926942578901263531118603 4390413868351895296677905)
                  ·
                    refine ⟨3292810401263921472508429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390413868351895296677905 3292810401263921472508429)
                    ·
                      refine ⟨1234803900473970552190661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292810401263921472508429 1234803900473970552190661)
                      ·
                        rfl

theorem cell23_2404772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_2404772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404772 prefixEnd_2404772 := by exact prefixLift 2404772
  have htrace : WordTrace (prefixWord ++ tailWord_2404772) baseStart_2404772 baseEnd_2404772 := by
    simpa [prefixWord, tailWord_2404772, baseEnd_2404772] using wordTrace_append hprefix tailTrace_2404772
  have hstable : (prefixWord ++ tailWord_2404772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404772).length < 2 ^ (prefixWord ++ tailWord_2404772).sum := by decide
  have hdescent : baseEnd_2404772 < baseStart_2404772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404785 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2404785 : Nat := 118140960795 + 2404785 * 2 ^ 59
def prefixEnd_2404785 : Nat := 4983230072969 + 3 ^ 40 * 2404785 * 2
def baseEnd_2404785 : Nat := 1234810575722479001328101

theorem tailTrace_2404785 : CollatzResearch.WordTrace tailWord_2404785 prefixEnd_2404785 1234810575722479001328101 := by
  unfold tailWord_2404785
  simp only [CollatzResearch.WordTrace]
  refine ⟨87709714592882124425247809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58473143061921416283498539 87709714592882124425247809)
  ·
    refine ⟨65782285944661593318935857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87709714592882124425247809 65782285944661593318935857)
    ·
      refine ⟨49336714458496194989201893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65782285944661593318935857 49336714458496194989201893)
      ·
        refine ⟨9250633960968036560475355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49336714458496194989201893 9250633960968036560475355)
        ·
          refine ⟨13875950941452054840713033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9250633960968036560475355 13875950941452054840713033)
          ·
            refine ⟨10406963206089041130534775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13875950941452054840713033 10406963206089041130534775)
            ·
              refine ⟨15610444809133561695802163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10406963206089041130534775 15610444809133561695802163)
              ·
                refine ⟨23415667213700342543703245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15610444809133561695802163 23415667213700342543703245)
                ·
                  refine ⟨8780875205137628453888717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23415667213700342543703245 8780875205137628453888717)
                  ·
                    refine ⟨3292828201926610670208269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8780875205137628453888717 3292828201926610670208269)
                    ·
                      refine ⟨1234810575722479001328101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292828201926610670208269 1234810575722479001328101)
                      ·
                        rfl

theorem cell23_2404785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2404785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404785 prefixEnd_2404785 := by exact prefixLift 2404785
  have htrace : WordTrace (prefixWord ++ tailWord_2404785) baseStart_2404785 baseEnd_2404785 := by
    simpa [prefixWord, tailWord_2404785, baseEnd_2404785] using wordTrace_append hprefix tailTrace_2404785
  have hstable : (prefixWord ++ tailWord_2404785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404785).length < 2 ^ (prefixWord ++ tailWord_2404785).sum := by decide
  have hdescent : baseEnd_2404785 < baseStart_2404785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404789 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_2404789 : Nat := 118140960795 + 2404789 * 2 ^ 59
def prefixEnd_2404789 : Nat := 4983230072969 + 3 ^ 40 * 2404789 * 2
def baseEnd_2404789 : Nat := 1234812629645096985678083

theorem tailTrace_2404789 : CollatzResearch.WordTrace tailWord_2404789 prefixEnd_2404789 1234812629645096985678083 := by
  unfold tailWord_2404789
  simp only [CollatzResearch.WordTrace]
  refine ⟨87709860484867633108393421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58473240323245088738928947 87709860484867633108393421)
  ·
    refine ⟨32891197681825362415647533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87709860484867633108393421 32891197681825362415647533)
    ·
      refine ⟨12334199130684510905867825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32891197681825362415647533 12334199130684510905867825)
      ·
        refine ⟨9250649348013383179400869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12334199130684510905867825 9250649348013383179400869)
        ·
          refine ⟨1734496752752509346137663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9250649348013383179400869 1734496752752509346137663)
          ·
            refine ⟨2601745129128764019206495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734496752752509346137663 2601745129128764019206495)
            ·
              refine ⟨3902617693693146028809743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601745129128764019206495 3902617693693146028809743)
              ·
                refine ⟨5853926540539719043214615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902617693693146028809743 5853926540539719043214615)
                ·
                  refine ⟨8780889810809578564821923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853926540539719043214615 8780889810809578564821923)
                  ·
                    refine ⟨13171334716214367847232885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8780889810809578564821923 13171334716214367847232885)
                    ·
                      refine ⟨1234812629645096985678083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13171334716214367847232885 1234812629645096985678083)
                      ·
                        rfl

theorem cell23_2404789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_2404789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404789 prefixEnd_2404789 := by exact prefixLift 2404789
  have htrace : WordTrace (prefixWord ++ tailWord_2404789) baseStart_2404789 baseEnd_2404789 := by
    simpa [prefixWord, tailWord_2404789, baseEnd_2404789] using wordTrace_append hprefix tailTrace_2404789
  have hstable : (prefixWord ++ tailWord_2404789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404789).length < 2 ^ (prefixWord ++ tailWord_2404789).sum := by decide
  have hdescent : baseEnd_2404789 < baseStart_2404789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404829 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_2404829 : Nat := 118140960795 + 2404829 * 2 ^ 59
def prefixEnd_2404829 : Nat := 4983230072969 + 3 ^ 40 * 2404829 * 2
def baseEnd_2404829 : Nat := 1234833168871276829177899

theorem tailTrace_2404829 : CollatzResearch.WordTrace tailWord_2404829 prefixEnd_2404829 1234833168871276829177899 := by
  unfold tailWord_2404829
  simp only [CollatzResearch.WordTrace]
  refine ⟨87711319404722719939849541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58474212936481813293233027 87711319404722719939849541)
  ·
    refine ⟨16445872388385509988721789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87711319404722719939849541 16445872388385509988721789)
    ·
      refine ⟨6167202145644566245770671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16445872388385509988721789 6167202145644566245770671)
      ·
        refine ⟨9250803218466849368656007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6167202145644566245770671 9250803218466849368656007)
        ·
          refine ⟨13876204827700274052984011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9250803218466849368656007 13876204827700274052984011)
          ·
            refine ⟨20814307241550411079476017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13876204827700274052984011 20814307241550411079476017)
            ·
              refine ⟨15610730431162808309607013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20814307241550411079476017 15610730431162808309607013)
              ·
                refine ⟨2927011955843026558051315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15610730431162808309607013 2927011955843026558051315)
                ·
                  refine ⟨4390517933764539837076973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927011955843026558051315 4390517933764539837076973)
                  ·
                    refine ⟨1646444225161702438903865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4390517933764539837076973 1646444225161702438903865)
                    ·
                      refine ⟨1234833168871276829177899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646444225161702438903865 1234833168871276829177899)
                      ·
                        rfl

theorem cell23_2404829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_2404829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404829 prefixEnd_2404829 := by exact prefixLift 2404829
  have htrace : WordTrace (prefixWord ++ tailWord_2404829) baseStart_2404829 baseEnd_2404829 := by
    simpa [prefixWord, tailWord_2404829, baseEnd_2404829] using wordTrace_append hprefix tailTrace_2404829
  have hstable : (prefixWord ++ tailWord_2404829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404829).length < 2 ^ (prefixWord ++ tailWord_2404829).sum := by decide
  have hdescent : baseEnd_2404829 < baseStart_2404829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404846 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_2404846 : Nat := 118140960795 + 2404846 * 2 ^ 59
def prefixEnd_2404846 : Nat := 4983230072969 + 3 ^ 40 * 2404846 * 2
def baseEnd_2404846 : Nat := 1234841898042403262665321

theorem tailTrace_2404846 : CollatzResearch.WordTrace tailWord_2404846 prefixEnd_2404846 1234841898042403262665321 := by
  unfold tailWord_2404846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963992430707641480402299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58474626297107421228812261 10963992430707641480402299)
  ·
    refine ⟨16445988646061462220603449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10963992430707641480402299 16445988646061462220603449)
    ·
      refine ⟨12334491484546096665452587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16445988646061462220603449 12334491484546096665452587)
      ·
        refine ⟨18501737226819144998178881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12334491484546096665452587 18501737226819144998178881)
        ·
          refine ⟨13876302920114358748634161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18501737226819144998178881 13876302920114358748634161)
          ·
            refine ⟨10407227190085769061475621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13876302920114358748634161 10407227190085769061475621)
            ·
              refine ⟨1951355098141081699026679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10407227190085769061475621 1951355098141081699026679)
              ·
                refine ⟨2927032647211622548540019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951355098141081699026679 2927032647211622548540019)
                ·
                  refine ⟨4390548970817433822810029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927032647211622548540019 4390548970817433822810029)
                  ·
                    refine ⟨1646455864056537683553761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4390548970817433822810029 1646455864056537683553761)
                    ·
                      refine ⟨1234841898042403262665321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646455864056537683553761 1234841898042403262665321)
                      ·
                        rfl

theorem cell23_2404846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_2404846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404846 prefixEnd_2404846 := by exact prefixLift 2404846
  have htrace : WordTrace (prefixWord ++ tailWord_2404846) baseStart_2404846 baseEnd_2404846 := by
    simpa [prefixWord, tailWord_2404846, baseEnd_2404846] using wordTrace_append hprefix tailTrace_2404846
  have hstable : (prefixWord ++ tailWord_2404846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404846).length < 2 ^ (prefixWord ++ tailWord_2404846).sum := by decide
  have hdescent : baseEnd_2404846 < baseStart_2404846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404848 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 9]
def baseStart_2404848 : Nat := 118140960795 + 2404848 * 2 ^ 59
def prefixEnd_2404848 : Nat := 4983230072969 + 3 ^ 40 * 2404848 * 2
def baseEnd_2404848 : Nat := 137204769444856917204479

theorem tailTrace_2404848 : CollatzResearch.WordTrace tailWord_2404848 prefixEnd_2404848 137204769444856917204479 := by
  unfold tailWord_2404848
  simp only [CollatzResearch.WordTrace]
  refine ⟨43856006195826943092395599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58474674927769257456527465 43856006195826943092395599)
  ·
    refine ⟨65784009293740414638593399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43856006195826943092395599 65784009293740414638593399)
    ·
      refine ⟨98676013940610621957890099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65784009293740414638593399 98676013940610621957890099)
      ·
        refine ⟨148014020910915932936835149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98676013940610621957890099 148014020910915932936835149)
        ·
          refine ⟨55505257841593474851313181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148014020910915932936835149 55505257841593474851313181)
          ·
            refine ⟨20814471690597553069242443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55505257841593474851313181 20814471690597553069242443)
            ·
              refine ⟨31221707535896329603863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20814471690597553069242443 31221707535896329603863665)
              ·
                refine ⟨23416280651922247202897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31221707535896329603863665 23416280651922247202897749)
                ·
                  refine ⟨137204769444856917204479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23416280651922247202897749 137204769444856917204479)
                  ·
                    rfl

theorem cell23_2404848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_2404848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404848 prefixEnd_2404848 := by exact prefixLift 2404848
  have htrace : WordTrace (prefixWord ++ tailWord_2404848) baseStart_2404848 baseEnd_2404848 := by
    simpa [prefixWord, tailWord_2404848, baseEnd_2404848] using wordTrace_append hprefix tailTrace_2404848
  have hstable : (prefixWord ++ tailWord_2404848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404848).length < 2 ^ (prefixWord ++ tailWord_2404848).sum := by decide
  have hdescent : baseEnd_2404848 < baseStart_2404848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404853 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2404853 : Nat := 118140960795 + 2404853 * 2 ^ 59
def prefixEnd_2404853 : Nat := 4983230072969 + 3 ^ 40 * 2404853 * 2
def baseEnd_2404853 : Nat := 1234845492406984735277789

theorem tailTrace_2404853 : CollatzResearch.WordTrace tailWord_2404853 prefixEnd_2404853 1234845492406984735277789 := by
  unfold tailWord_2404853
  simp only [CollatzResearch.WordTrace]
  refine ⟨87712194756635772038723213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58474796504423848025815475 87712194756635772038723213)
  ·
    refine ⟨32892073033738414514521205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87712194756635772038723213 32892073033738414514521205)
    ·
      refine ⟨3083631846912976360736363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32892073033738414514521205 3083631846912976360736363)
      ·
        refine ⟨4625447770369464541104545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083631846912976360736363 4625447770369464541104545)
        ·
          refine ⟨3469085827777098405828409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625447770369464541104545 3469085827777098405828409)
          ·
            refine ⟨2601814370832823804371307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469085827777098405828409 2601814370832823804371307)
            ·
              refine ⟨3902721556249235706556961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601814370832823804371307 3902721556249235706556961)
              ·
                refine ⟨2927041167186926779917721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3902721556249235706556961 2927041167186926779917721)
                ·
                  refine ⟨2195280875390195084938291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2927041167186926779917721 2195280875390195084938291)
                  ·
                    refine ⟨3292921313085292627407437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195280875390195084938291 3292921313085292627407437)
                    ·
                      refine ⟨1234845492406984735277789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3292921313085292627407437 1234845492406984735277789)
                      ·
                        rfl

theorem cell23_2404853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2404853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404853 prefixEnd_2404853 := by exact prefixLift 2404853
  have htrace : WordTrace (prefixWord ++ tailWord_2404853) baseStart_2404853 baseEnd_2404853 := by
    simpa [prefixWord, tailWord_2404853, baseEnd_2404853] using wordTrace_append hprefix tailTrace_2404853
  have hstable : (prefixWord ++ tailWord_2404853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404853).length < 2 ^ (prefixWord ++ tailWord_2404853).sum := by decide
  have hdescent : baseEnd_2404853 < baseStart_2404853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404858 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_2404858 : Nat := 118140960795 + 2404858 * 2 ^ 59
def prefixEnd_2404858 : Nat := 4983230072969 + 3 ^ 40 * 2404858 * 2
def baseEnd_2404858 : Nat := 1234848059810257215715265

theorem tailTrace_2404858 : CollatzResearch.WordTrace tailWord_2404858 prefixEnd_2404858 1234848059810257215715265 := by
  unfold tailWord_2404858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21928094280404414473163807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58474918081078438595103485 21928094280404414473163807)
  ·
    refine ⟨32892141420606621709745711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21928094280404414473163807 32892141420606621709745711)
    ·
      refine ⟨49338212130909932564618567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32892141420606621709745711 49338212130909932564618567)
      ·
        refine ⟨74007318196364898846927851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49338212130909932564618567 74007318196364898846927851)
        ·
          refine ⟨111010977294547348270391777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74007318196364898846927851 111010977294547348270391777)
          ·
            refine ⟨83258232970910511202793833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111010977294547348270391777 83258232970910511202793833)
            ·
              refine ⟨62443674728182883402095375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83258232970910511202793833 62443674728182883402095375)
              ·
                refine ⟨93665512092274325103143063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62443674728182883402095375 93665512092274325103143063)
                ·
                  refine ⟨140498268138411487654714595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93665512092274325103143063 140498268138411487654714595)
                  ·
                    refine ⟨210747402207617231482071893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140498268138411487654714595 210747402207617231482071893)
                    ·
                      refine ⟨1234848059810257215715265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 210747402207617231482071893 1234848059810257215715265)
                      ·
                        rfl

theorem cell23_2404858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2404858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404858 prefixEnd_2404858 := by exact prefixLift 2404858
  have htrace : WordTrace (prefixWord ++ tailWord_2404858) baseStart_2404858 baseEnd_2404858 := by
    simpa [prefixWord, tailWord_2404858, baseEnd_2404858] using wordTrace_append hprefix tailTrace_2404858
  have hstable : (prefixWord ++ tailWord_2404858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404858).length < 2 ^ (prefixWord ++ tailWord_2404858).sum := by decide
  have hdescent : baseEnd_2404858 < baseStart_2404858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404865 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 7]
def baseStart_2404865 : Nat := 118140960795 + 2404865 * 2 ^ 59
def prefixEnd_2404865 : Nat := 4983230072969 + 3 ^ 40 * 2404865 * 2
def baseEnd_2404865 : Nat := 137205739352759854258637

theorem tailTrace_2404865 : CollatzResearch.WordTrace tailWord_2404865 prefixEnd_2404865 137205739352759854258637 := by
  unfold tailWord_2404865
  simp only [CollatzResearch.WordTrace]
  refine ⟨87712632432592298088160049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58475088288394865392106699 87712632432592298088160049)
  ·
    refine ⟨65784474324444223566120037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87712632432592298088160049 65784474324444223566120037)
    ·
      refine ⟨12334588935833291918647507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65784474324444223566120037 12334588935833291918647507)
      ·
        refine ⟨18501883403749937877971261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12334588935833291918647507 18501883403749937877971261)
        ·
          refine ⟨6938206276406226704239223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18501883403749937877971261 6938206276406226704239223)
          ·
            refine ⟨10407309414609340056358835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6938206276406226704239223 10407309414609340056358835)
            ·
              refine ⟨15610964121914010084538253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407309414609340056358835 15610964121914010084538253)
              ·
                refine ⟨5854111545717753781701845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15610964121914010084538253 5854111545717753781701845)
                ·
                  refine ⟨137205739352759854258637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5854111545717753781701845 137205739352759854258637)
                  ·
                    rfl

theorem cell23_2404865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_2404865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404865 prefixEnd_2404865 := by exact prefixLift 2404865
  have htrace : WordTrace (prefixWord ++ tailWord_2404865) baseStart_2404865 baseEnd_2404865 := by
    simpa [prefixWord, tailWord_2404865, baseEnd_2404865] using wordTrace_append hprefix tailTrace_2404865
  have hstable : (prefixWord ++ tailWord_2404865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404865).length < 2 ^ (prefixWord ++ tailWord_2404865).sum := by decide
  have hdescent : baseEnd_2404865 < baseStart_2404865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404895 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 2, 5]
def baseStart_2404895 : Nat := 118140960795 + 2404895 * 2 ^ 59
def prefixEnd_2404895 : Nat := 4983230072969 + 3 ^ 40 * 2404895 * 2
def baseEnd_2404895 : Nat := 411622352864824523650865

theorem tailTrace_2404895 : CollatzResearch.WordTrace tailWord_2404895 prefixEnd_2404895 411622352864824523650865 := by
  unfold tailWord_2404895
  simp only [CollatzResearch.WordTrace]
  refine ⟨87713726622483613211752139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58475817748322408807834759 87713726622483613211752139)
  ·
    refine ⟨131570589933725419817628209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87713726622483613211752139 131570589933725419817628209)
    ·
      refine ⟨98677942450294064863221157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131570589933725419817628209 98677942450294064863221157)
      ·
        refine ⟨18502114209430137161853967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98677942450294064863221157 18502114209430137161853967)
        ·
          refine ⟨27753171314145205742780951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18502114209430137161853967 27753171314145205742780951)
          ·
            refine ⟨41629756971217808614171427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27753171314145205742780951 41629756971217808614171427)
            ·
              refine ⟨62444635456826712921257141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41629756971217808614171427 62444635456826712921257141)
              ·
                refine ⟨5854184574077504336367857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62444635456826712921257141 5854184574077504336367857)
                ·
                  refine ⟨4390638430558128252275893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854184574077504336367857 4390638430558128252275893)
                  ·
                    refine ⟨411622352864824523650865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4390638430558128252275893 411622352864824523650865)
                    ·
                      rfl

theorem cell23_2404895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_2404895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404895 prefixEnd_2404895 := by exact prefixLift 2404895
  have htrace : WordTrace (prefixWord ++ tailWord_2404895) baseStart_2404895 baseEnd_2404895 := by
    simpa [prefixWord, tailWord_2404895, baseEnd_2404895] using wordTrace_append hprefix tailTrace_2404895
  have hstable : (prefixWord ++ tailWord_2404895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404895).length < 2 ^ (prefixWord ++ tailWord_2404895).sum := by decide
  have hdescent : baseEnd_2404895 < baseStart_2404895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404899 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 5]
def baseStart_2404899 : Nat := 118140960795 + 2404899 * 2 ^ 59
def prefixEnd_2404899 : Nat := 4983230072969 + 3 ^ 40 * 2404899 * 2
def baseEnd_2404899 : Nat := 137207679168565728366953

theorem tailTrace_2404899 : CollatzResearch.WordTrace tailWord_2404899 prefixEnd_2404899 137207679168565728366953 := by
  unfold tailWord_2404899
  simp only [CollatzResearch.WordTrace]
  refine ⟨87713872514469121894897751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58475915009646081263265167 87713872514469121894897751)
  ·
    refine ⟨131570808771703682842346627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87713872514469121894897751 131570808771703682842346627)
    ·
      refine ⟨197356213157555524263519941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131570808771703682842346627 197356213157555524263519941)
      ·
        refine ⟨37004289967041660799409989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197356213157555524263519941 37004289967041660799409989)
        ·
          refine ⟨6938304368820311399889373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37004289967041660799409989 6938304368820311399889373)
          ·
            refine ⟨2601864138307616774958515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6938304368820311399889373 2601864138307616774958515)
            ·
              refine ⟨3902796207461425162437773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601864138307616774958515 3902796207461425162437773)
              ·
                refine ⟨1463548577798034435914165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3902796207461425162437773 1463548577798034435914165)
                ·
                  refine ⟨137207679168565728366953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1463548577798034435914165 137207679168565728366953)
                  ·
                    rfl

theorem cell23_2404899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 5].length) (baseStart_2404899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404899 prefixEnd_2404899 := by exact prefixLift 2404899
  have htrace : WordTrace (prefixWord ++ tailWord_2404899) baseStart_2404899 baseEnd_2404899 := by
    simpa [prefixWord, tailWord_2404899, baseEnd_2404899] using wordTrace_append hprefix tailTrace_2404899
  have hstable : (prefixWord ++ tailWord_2404899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404899).length < 2 ^ (prefixWord ++ tailWord_2404899).sum := by decide
  have hdescent : baseEnd_2404899 < baseStart_2404899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404916 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2404916 : Nat := 118140960795 + 2404916 * 2 ^ 59
def prefixEnd_2404916 : Nat := 4983230072969 + 3 ^ 40 * 2404916 * 2
def baseEnd_2404916 : Nat := 137208649076468665421111

theorem tailTrace_2404916 : CollatzResearch.WordTrace tailWord_2404916 prefixEnd_2404916 137208649076468665421111 := by
  unfold tailWord_2404916
  simp only [CollatzResearch.WordTrace]
  refine ⟨43857246277703766899133301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58476328370271689198844401 43857246277703766899133301)
  ·
    refine ⟨4111616838534728146793747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43857246277703766899133301 4111616838534728146793747)
    ·
      refine ⟨6167425257802092220190621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111616838534728146793747 6167425257802092220190621)
      ·
        refine ⟨2312784471675784582571483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6167425257802092220190621 2312784471675784582571483)
        ·
          refine ⟨3469176707513676873857225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312784471675784582571483 3469176707513676873857225)
          ·
            refine ⟨2601882530635257655392919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469176707513676873857225 2601882530635257655392919)
            ·
              refine ⟨3902823795952886483089379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601882530635257655392919 3902823795952886483089379)
              ·
                refine ⟨5854235693929329724634069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902823795952886483089379 5854235693929329724634069)
                ·
                  refine ⟨137208649076468665421111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5854235693929329724634069 137208649076468665421111)
                  ·
                    rfl

theorem cell23_2404916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2404916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404916 prefixEnd_2404916 := by exact prefixLift 2404916
  have htrace : WordTrace (prefixWord ++ tailWord_2404916) baseStart_2404916 baseEnd_2404916 := by
    simpa [prefixWord, tailWord_2404916, baseEnd_2404916] using wordTrace_append hprefix tailTrace_2404916
  have hstable : (prefixWord ++ tailWord_2404916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404916).length < 2 ^ (prefixWord ++ tailWord_2404916).sum := by decide
  have hdescent : baseEnd_2404916 < baseStart_2404916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404942 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2404942 : Nat := 118140960795 + 2404942 * 2 ^ 59
def prefixEnd_2404942 : Nat := 4983230072969 + 3 ^ 40 * 2404942 * 2
def baseEnd_2404942 : Nat := 411630397395078295688293

theorem tailTrace_2404942 : CollatzResearch.WordTrace tailWord_2404942 prefixEnd_2404942 411630397395078295688293 := by
  unfold tailWord_2404942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964430106664167529839135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58476960568875560159142053 10964430106664167529839135)
  ·
    refine ⟨16446645159996251294758703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10964430106664167529839135 16446645159996251294758703)
    ·
      refine ⟨24669967739994376942138055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16446645159996251294758703 24669967739994376942138055)
      ·
        refine ⟨37004951609991565413207083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24669967739994376942138055 37004951609991565413207083)
        ·
          refine ⟨55507427414987348119810625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37004951609991565413207083 55507427414987348119810625)
          ·
            refine ⟨41630570561240511089857969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55507427414987348119810625 41630570561240511089857969)
            ·
              refine ⟨31222927920930383317393477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41630570561240511089857969 31222927920930383317393477)
              ·
                refine ⟨5854298985174446872011277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31222927920930383317393477 5854298985174446872011277)
                ·
                  refine ⟨2195362119440417577004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5854298985174446872011277 2195362119440417577004229)
                  ·
                    refine ⟨411630397395078295688293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195362119440417577004229 411630397395078295688293)
                    ·
                      rfl

theorem cell23_2404942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2404942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404942 prefixEnd_2404942 := by exact prefixLift 2404942
  have htrace : WordTrace (prefixWord ++ tailWord_2404942) baseStart_2404942 baseEnd_2404942 := by
    simpa [prefixWord, tailWord_2404942, baseEnd_2404942] using wordTrace_append hprefix tailTrace_2404942
  have hstable : (prefixWord ++ tailWord_2404942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404942).length < 2 ^ (prefixWord ++ tailWord_2404942).sum := by decide
  have hdescent : baseEnd_2404942 < baseStart_2404942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404952 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2404952 : Nat := 118140960795 + 2404952 * 2 ^ 59
def prefixEnd_2404952 : Nat := 4983230072969 + 3 ^ 40 * 2404952 * 2
def baseEnd_2404952 : Nat := 1234896326991779847939833

theorem tailTrace_2404952 : CollatzResearch.WordTrace tailWord_2404952 prefixEnd_2404952 1234896326991779847939833 := by
  unfold tailWord_2404952
  simp only [CollatzResearch.WordTrace]
  refine ⟨43857902791638555973288555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58477203722184741297718073 43857902791638555973288555)
  ·
    refine ⟨65786854187457833959932833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43857902791638555973288555 65786854187457833959932833)
    ·
      refine ⟨49340140640593375469949625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65786854187457833959932833 49340140640593375469949625)
      ·
        refine ⟨37005105480445031602462219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49340140640593375469949625 37005105480445031602462219)
        ·
          refine ⟨55507658220667547403693329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37005105480445031602462219 55507658220667547403693329)
          ·
            refine ⟨41630743665500660552769997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55507658220667547403693329 41630743665500660552769997)
            ·
              refine ⟨15611528874562747707288749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41630743665500660552769997 15611528874562747707288749)
              ·
                refine ⟨5854323327961030390233281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15611528874562747707288749 5854323327961030390233281)
                ·
                  refine ⟨4390742495970772792674961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854323327961030390233281 4390742495970772792674961)
                  ·
                    refine ⟨3293056871978079594506221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390742495970772792674961 3293056871978079594506221)
                    ·
                      refine ⟨1234896326991779847939833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3293056871978079594506221 1234896326991779847939833)
                      ·
                        rfl

theorem cell23_2404952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2404952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404952 prefixEnd_2404952 := by exact prefixLift 2404952
  have htrace : WordTrace (prefixWord ++ tailWord_2404952) baseStart_2404952 baseEnd_2404952 := by
    simpa [prefixWord, tailWord_2404952, baseEnd_2404952] using wordTrace_append hprefix tailTrace_2404952
  have hstable : (prefixWord ++ tailWord_2404952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404952).length < 2 ^ (prefixWord ++ tailWord_2404952).sum := by decide
  have hdescent : baseEnd_2404952 < baseStart_2404952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404976 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 1, 4]
def baseStart_2404976 : Nat := 118140960795 + 2404976 * 2 ^ 59
def prefixEnd_2404976 : Nat := 4983230072969 + 3 ^ 40 * 2404976 * 2
def baseEnd_2404976 : Nat := 411636216842495918013241

theorem tailTrace_2404976 : CollatzResearch.WordTrace tailWord_2404976 prefixEnd_2404976 411636216842495918013241 := by
  unfold tailWord_2404976
  simp only [CollatzResearch.WordTrace]
  refine ⟨43858340467595082022725391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58477787290126776030300521 43858340467595082022725391)
  ·
    refine ⟨65787510701392623034088087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43858340467595082022725391 65787510701392623034088087)
    ·
      refine ⟨98681266052088934551132131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65787510701392623034088087 98681266052088934551132131)
      ·
        refine ⟨148021899078133401826698197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98681266052088934551132131 148021899078133401826698197)
        ·
          refine ⟨3469263259643751605313239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 148021899078133401826698197 3469263259643751605313239)
          ·
            refine ⟨5203894889465627407969859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469263259643751605313239 5203894889465627407969859)
            ·
              refine ⟨7805842334198441111954789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203894889465627407969859 7805842334198441111954789)
              ·
                refine ⟨1463595437662207708491523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7805842334198441111954789 1463595437662207708491523)
                ·
                  refine ⟨2195393156493311562737285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463595437662207708491523 2195393156493311562737285)
                  ·
                    refine ⟨411636216842495918013241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195393156493311562737285 411636216842495918013241)
                    ·
                      rfl

theorem cell23_2404976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 4].length) (baseStart_2404976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404976 prefixEnd_2404976 := by exact prefixLift 2404976
  have htrace : WordTrace (prefixWord ++ tailWord_2404976) baseStart_2404976 baseEnd_2404976 := by
    simpa [prefixWord, tailWord_2404976, baseEnd_2404976] using wordTrace_append hprefix tailTrace_2404976
  have hstable : (prefixWord ++ tailWord_2404976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404976).length < 2 ^ (prefixWord ++ tailWord_2404976).sum := by decide
  have hdescent : baseEnd_2404976 < baseStart_2404976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2404999 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_2404999 : Nat := 118140960795 + 2404999 * 2 ^ 59
def prefixEnd_2404999 : Nat := 4983230072969 + 3 ^ 40 * 2404999 * 2
def baseEnd_2404999 : Nat := 1234920460582541164052117

theorem tailTrace_2404999 : CollatzResearch.WordTrace tailWord_2404999 prefixEnd_2404999 1234920460582541164052117 := by
  unfold tailWord_2404999
  simp only [CollatzResearch.WordTrace]
  refine ⟨87717519814106838973538051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58478346542737892649025367 87717519814106838973538051)
  ·
    refine ⟨131576279721160258460307077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87717519814106838973538051 131576279721160258460307077)
    ·
      refine ⟨24670552447717548461307577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131576279721160258460307077 24670552447717548461307577)
      ·
        refine ⟨18502914335788161345980683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24670552447717548461307577 18502914335788161345980683)
        ·
          refine ⟨27754371503682242018971025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18502914335788161345980683 27754371503682242018971025)
          ·
            refine ⟨20815778627761681514228269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27754371503682242018971025 20815778627761681514228269)
            ·
              refine ⟨7805916985410630567835601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20815778627761681514228269 7805916985410630567835601)
              ·
                refine ⟨5854437739057972925876701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7805916985410630567835601 5854437739057972925876701)
                ·
                  refine ⟨2195414152146739847203763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5854437739057972925876701 2195414152146739847203763)
                  ·
                    refine ⟨3293121228220109770805645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195414152146739847203763 3293121228220109770805645)
                    ·
                      refine ⟨1234920460582541164052117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3293121228220109770805645 1234920460582541164052117)
                      ·
                        rfl

theorem cell23_2404999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_2404999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2404999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2404999 prefixEnd_2404999 := by exact prefixLift 2404999
  have htrace : WordTrace (prefixWord ++ tailWord_2404999) baseStart_2404999 baseEnd_2404999 := by
    simpa [prefixWord, tailWord_2404999, baseEnd_2404999] using wordTrace_append hprefix tailTrace_2404999
  have hstable : (prefixWord ++ tailWord_2404999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2404999).length < 2 ^ (prefixWord ++ tailWord_2404999).sum := by decide
  have hdescent : baseEnd_2404999 < baseStart_2404999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2404999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405052 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2405052 : Nat := 118140960795 + 2405052 * 2 ^ 59
def prefixEnd_2405052 : Nat := 4983230072969 + 3 ^ 40 * 2405052 * 2
def baseEnd_2405052 : Nat := 1234947675057229456689373

theorem tailTrace_2405052 : CollatzResearch.WordTrace tailWord_2405052 prefixEnd_2405052 1234947675057229456689373 := by
  unfold tailWord_2405052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43859726441457414512608705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58479635255276552683478273 43859726441457414512608705)
  ·
    refine ⟨32894794831093060884456529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43859726441457414512608705 32894794831093060884456529)
    ·
      refine ⟨24671096123319795663342397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32894794831093060884456529 24671096123319795663342397)
      ·
        refine ⟨9251661046244923373753399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24671096123319795663342397 9251661046244923373753399)
        ·
          refine ⟨13877491569367385060630099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9251661046244923373753399 13877491569367385060630099)
          ·
            refine ⟨20816237354051077590945149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13877491569367385060630099 20816237354051077590945149)
            ·
              refine ⟨7806089007769154096604431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20816237354051077590945149 7806089007769154096604431)
              ·
                refine ⟨11709133511653731144906647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806089007769154096604431 11709133511653731144906647)
                ·
                  refine ⟨17563700267480596717359971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11709133511653731144906647 17563700267480596717359971)
                  ·
                    refine ⟨26345550401220895076039957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17563700267480596717359971 26345550401220895076039957)
                    ·
                      refine ⟨1234947675057229456689373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26345550401220895076039957 1234947675057229456689373)
                      ·
                        rfl

theorem cell23_2405052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2405052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405052 prefixEnd_2405052 := by exact prefixLift 2405052
  have htrace : WordTrace (prefixWord ++ tailWord_2405052) baseStart_2405052 baseEnd_2405052 := by
    simpa [prefixWord, tailWord_2405052, baseEnd_2405052] using wordTrace_append hprefix tailTrace_2405052
  have hstable : (prefixWord ++ tailWord_2405052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405052).length < 2 ^ (prefixWord ++ tailWord_2405052).sum := by decide
  have hdescent : baseEnd_2405052 < baseStart_2405052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405056 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2]
def baseStart_2405056 : Nat := 118140960795 + 2405056 * 2 ^ 59
def prefixEnd_2405056 : Nat := 4983230072969 + 3 ^ 40 * 2405056 * 2
def baseEnd_2405056 : Nat := 1234949728979847441039355

theorem tailTrace_2405056 : CollatzResearch.WordTrace tailWord_2405056 prefixEnd_2405056 1234949728979847441039355 := by
  unfold tailWord_2405056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43859799387450168854181511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58479732516600225138908681 43859799387450168854181511)
  ·
    refine ⟨65789699081175253281272267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43859799387450168854181511 65789699081175253281272267)
    ·
      refine ⟨98684548621762879921908401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65789699081175253281272267 98684548621762879921908401)
      ·
        refine ⟨74013411466322159941431301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98684548621762879921908401 74013411466322159941431301)
        ·
          refine ⟨13877514649935404989018369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74013411466322159941431301 13877514649935404989018369)
          ·
            refine ⟨10408135987451553741763777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13877514649935404989018369 10408135987451553741763777)
            ·
              refine ⟨7806101990588665306322833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10408135987451553741763777 7806101990588665306322833)
              ·
                refine ⟨5854576492941498979742125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7806101990588665306322833 5854576492941498979742125)
                ·
                  refine ⟨2195466184853062117403297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5854576492941498979742125 2195466184853062117403297)
                  ·
                    refine ⟨1646599638639796588052473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195466184853062117403297 1646599638639796588052473)
                    ·
                      refine ⟨1234949728979847441039355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646599638639796588052473 1234949728979847441039355)
                      ·
                        rfl

theorem cell23_2405056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_2405056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405056 prefixEnd_2405056 := by exact prefixLift 2405056
  have htrace : WordTrace (prefixWord ++ tailWord_2405056) baseStart_2405056 baseEnd_2405056 := by
    simpa [prefixWord, tailWord_2405056, baseEnd_2405056] using wordTrace_append hprefix tailTrace_2405056
  have hstable : (prefixWord ++ tailWord_2405056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405056).length < 2 ^ (prefixWord ++ tailWord_2405056).sum := by decide
  have hdescent : baseEnd_2405056 < baseStart_2405056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405065 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_2405065 : Nat := 118140960795 + 2405065 * 2 ^ 59
def prefixEnd_2405065 : Nat := 4983230072969 + 3 ^ 40 * 2405065 * 2
def baseEnd_2405065 : Nat := 1234954350305737905826813

theorem tailTrace_2405065 : CollatzResearch.WordTrace tailWord_2405065 prefixEnd_2405065 1234954350305737905826813 := by
  unfold tailWord_2405065
  simp only [CollatzResearch.WordTrace]
  refine ⟨87719927031867732245440649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58479951354578488163627099 87719927031867732245440649)
  ·
    refine ⟨65789945273900799184080487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87719927031867732245440649 65789945273900799184080487)
    ·
      refine ⟨98684917910851198776120731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65789945273900799184080487 98684917910851198776120731)
      ·
        refine ⟨148027376866276798164181097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98684917910851198776120731 148027376866276798164181097)
        ·
          refine ⟨111020532649707598623135823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148027376866276798164181097 111020532649707598623135823)
          ·
            refine ⟨166530798974561397934703735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111020532649707598623135823 166530798974561397934703735)
            ·
              refine ⟨249796198461842096902055603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166530798974561397934703735 249796198461842096902055603)
              ·
                refine ⟨374694297692763145353083405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249796198461842096902055603 374694297692763145353083405)
                ·
                  refine ⟨140510361634786179507406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374694297692763145353083405 140510361634786179507406277)
                  ·
                    refine ⟨26345692806522408657638677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140510361634786179507406277 26345692806522408657638677)
                    ·
                      refine ⟨1234954350305737905826813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26345692806522408657638677 1234954350305737905826813)
                      ·
                        rfl

theorem cell23_2405065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_2405065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405065 prefixEnd_2405065 := by exact prefixLift 2405065
  have htrace : WordTrace (prefixWord ++ tailWord_2405065) baseStart_2405065 baseEnd_2405065 := by
    simpa [prefixWord, tailWord_2405065, baseEnd_2405065] using wordTrace_append hprefix tailTrace_2405065
  have hstable : (prefixWord ++ tailWord_2405065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405065).length < 2 ^ (prefixWord ++ tailWord_2405065).sum := by decide
  have hdescent : baseEnd_2405065 < baseStart_2405065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405076 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2405076 : Nat := 118140960795 + 2405076 * 2 ^ 59
def prefixEnd_2405076 : Nat := 4983230072969 + 3 ^ 40 * 2405076 * 2
def baseEnd_2405076 : Nat := 1234959998592937362789263

theorem tailTrace_2405076 : CollatzResearch.WordTrace tailWord_2405076 prefixEnd_2405076 1234959998592937362789263 := by
  unfold tailWord_2405076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43860164117413940562045541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58480218823218587416060721 43860164117413940562045541)
  ·
    refine ⟨8223780772015113855383539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43860164117413940562045541 8223780772015113855383539)
    ·
      refine ⟨12335671158022670783075309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8223780772015113855383539 12335671158022670783075309)
      ·
        refine ⟨4625876684258501543653241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12335671158022670783075309 4625876684258501543653241)
        ·
          refine ⟨3469407513193876157739931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625876684258501543653241 3469407513193876157739931)
          ·
            refine ⟨5204111269790814236609897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469407513193876157739931 5204111269790814236609897)
            ·
              refine ⟨3903083452343110677457423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5204111269790814236609897 3903083452343110677457423)
              ·
                refine ⟨5854625178514666016186135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903083452343110677457423 5854625178514666016186135)
                ·
                  refine ⟨8781937767771999024279203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854625178514666016186135 8781937767771999024279203)
                  ·
                    refine ⟨13172906651657998536418805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8781937767771999024279203 13172906651657998536418805)
                    ·
                      refine ⟨1234959998592937362789263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13172906651657998536418805 1234959998592937362789263)
                      ·
                        rfl

theorem cell23_2405076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2405076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405076 prefixEnd_2405076 := by exact prefixLift 2405076
  have htrace : WordTrace (prefixWord ++ tailWord_2405076) baseStart_2405076 baseEnd_2405076 := by
    simpa [prefixWord, tailWord_2405076, baseEnd_2405076] using wordTrace_append hprefix tailTrace_2405076
  have hstable : (prefixWord ++ tailWord_2405076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405076).length < 2 ^ (prefixWord ++ tailWord_2405076).sum := by decide
  have hdescent : baseEnd_2405076 < baseStart_2405076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405099 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 3, 3, 2]
def baseStart_2405099 : Nat := 118140960795 + 2405099 * 2 ^ 59
def prefixEnd_2405099 : Nat := 4983230072969 + 3 ^ 40 * 2405099 * 2
def baseEnd_2405099 : Nat := 1234971808647990772801657

theorem tailTrace_2405099 : CollatzResearch.WordTrace tailWord_2405099 prefixEnd_2405099 1234971808647990772801657 := by
  unfold tailWord_2405099
  simp only [CollatzResearch.WordTrace]
  refine ⟨87721167113744556052178351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58480778075829704034785567 87721167113744556052178351)
  ·
    refine ⟨131581750670616834078267527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87721167113744556052178351 131581750670616834078267527)
    ·
      refine ⟨197372626005925251117401291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131581750670616834078267527 197372626005925251117401291)
      ·
        refine ⟨296058939008887876676101937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197372626005925251117401291 296058939008887876676101937)
        ·
          refine ⟨222044204256665907507076453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296058939008887876676101937 222044204256665907507076453)
          ·
            refine ⟨41633288298124857657576835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222044204256665907507076453 41633288298124857657576835)
            ·
              refine ⟨62449932447187286486365253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41633288298124857657576835 62449932447187286486365253)
              ·
                refine ⟨11709362333847616216193485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62449932447187286486365253 11709362333847616216193485)
                ·
                  refine ⟨4391010875192856081072557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11709362333847616216193485 4391010875192856081072557)
                  ·
                    refine ⟨1646629078197321030402209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4391010875192856081072557 1646629078197321030402209)
                    ·
                      refine ⟨1234971808647990772801657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646629078197321030402209 1234971808647990772801657)
                      ·
                        rfl

theorem cell23_2405099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3, 2].length) (baseStart_2405099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405099 prefixEnd_2405099 := by exact prefixLift 2405099
  have htrace : WordTrace (prefixWord ++ tailWord_2405099) baseStart_2405099 baseEnd_2405099 := by
    simpa [prefixWord, tailWord_2405099, baseEnd_2405099] using wordTrace_append hprefix tailTrace_2405099
  have hstable : (prefixWord ++ tailWord_2405099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405099).length < 2 ^ (prefixWord ++ tailWord_2405099).sum := by decide
  have hdescent : baseEnd_2405099 < baseStart_2405099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405116 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_2405116 : Nat := 118140960795 + 2405116 * 2 ^ 59
def prefixEnd_2405116 : Nat := 4983230072969 + 3 ^ 40 * 2405116 * 2
def baseEnd_2405116 : Nat := 1234980537819117206289079

theorem tailTrace_2405116 : CollatzResearch.WordTrace tailWord_2405116 prefixEnd_2405116 1234980537819117206289079 := by
  unfold tailWord_2405116
  simp only [CollatzResearch.WordTrace]
  refine ⟨43860893577341483977773601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58481191436455311970364801 43860893577341483977773601)
  ·
    refine ⟨32895670183006112983330201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43860893577341483977773601 32895670183006112983330201)
    ·
      refine ⟨24671752637254584737497651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32895670183006112983330201 24671752637254584737497651)
      ·
        refine ⟨37007628955881877106246477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24671752637254584737497651 37007628955881877106246477)
        ·
          refine ⟨13877860858455703914842429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37007628955881877106246477 13877860858455703914842429)
          ·
            refine ⟨5204197821920888968065911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13877860858455703914842429 5204197821920888968065911)
            ·
              refine ⟨7806296732881333452098867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204197821920888968065911 7806296732881333452098867)
              ·
                refine ⟨11709445099322000178148301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806296732881333452098867 11709445099322000178148301)
                ·
                  refine ⟨4391041912245750066805613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11709445099322000178148301 4391041912245750066805613)
                  ·
                    refine ⟨1646640717092156275052105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4391041912245750066805613 1646640717092156275052105)
                    ·
                      refine ⟨1234980537819117206289079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646640717092156275052105 1234980537819117206289079)
                      ·
                        rfl

theorem cell23_2405116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_2405116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405116 prefixEnd_2405116 := by exact prefixLift 2405116
  have htrace : WordTrace (prefixWord ++ tailWord_2405116) baseStart_2405116 baseEnd_2405116 := by
    simpa [prefixWord, tailWord_2405116, baseEnd_2405116] using wordTrace_append hprefix tailTrace_2405116
  have hstable : (prefixWord ++ tailWord_2405116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405116).length < 2 ^ (prefixWord ++ tailWord_2405116).sum := by decide
  have hdescent : baseEnd_2405116 < baseStart_2405116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405129 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 3, 4, 2]
def baseStart_2405129 : Nat := 118140960795 + 2405129 * 2 ^ 59
def prefixEnd_2405129 : Nat := 4983230072969 + 3 ^ 40 * 2405129 * 2
def baseEnd_2405129 : Nat := 1234987213067625655426519

theorem tailTrace_2405129 : CollatzResearch.WordTrace tailWord_2405129 prefixEnd_2405129 1234987213067625655426519 := by
  unfold tailWord_2405129
  simp only [CollatzResearch.WordTrace]
  refine ⟨87722261303635871175770441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58481507535757247450513627 87722261303635871175770441)
  ·
    refine ⟨65791695977726903381827831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87722261303635871175770441 65791695977726903381827831)
    ·
      refine ⟨98687543966590355072741747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65791695977726903381827831 98687543966590355072741747)
      ·
        refine ⟨148031315949885532609112621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98687543966590355072741747 148031315949885532609112621)
        ·
          refine ⟨55511743481207074728417233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148031315949885532609112621 55511743481207074728417233)
          ·
            refine ⟨41633807610905306046312925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55511743481207074728417233 41633807610905306046312925)
            ·
              refine ⟨15612677854089489767367347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41633807610905306046312925 15612677854089489767367347)
              ·
                refine ⟨23419016781134234651051021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15612677854089489767367347 23419016781134234651051021)
                ·
                  refine ⟨8782131292925337994144133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23419016781134234651051021 8782131292925337994144133)
                  ·
                    refine ⟨1646649617423500873902025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8782131292925337994144133 1646649617423500873902025)
                    ·
                      refine ⟨1234987213067625655426519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646649617423500873902025 1234987213067625655426519)
                      ·
                        rfl

theorem cell23_2405129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4, 2].length) (baseStart_2405129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405129 prefixEnd_2405129 := by exact prefixLift 2405129
  have htrace : WordTrace (prefixWord ++ tailWord_2405129) baseStart_2405129 baseEnd_2405129 := by
    simpa [prefixWord, tailWord_2405129, baseEnd_2405129] using wordTrace_append hprefix tailTrace_2405129
  have hstable : (prefixWord ++ tailWord_2405129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405129).length < 2 ^ (prefixWord ++ tailWord_2405129).sum := by decide
  have hdescent : baseEnd_2405129 < baseStart_2405129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405189 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_2405189 : Nat := 118140960795 + 2405189 * 2 ^ 59
def prefixEnd_2405189 : Nat := 4983230072969 + 3 ^ 40 * 2405189 * 2
def baseEnd_2405189 : Nat := 1235018021906895420676243

theorem tailTrace_2405189 : CollatzResearch.WordTrace tailWord_2405189 prefixEnd_2405189 1235018021906895420676243 := by
  unfold tailWord_2405189
  simp only [CollatzResearch.WordTrace]
  refine ⟨87724449683418501422954621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58482966455612334281969747 87724449683418501422954621)
  ·
    refine ⟨32896668631281938033607983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87724449683418501422954621 32896668631281938033607983)
    ·
      refine ⟨49345002946922907050411975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32896668631281938033607983 49345002946922907050411975)
      ·
        refine ⟨74017504420384360575617963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49345002946922907050411975 74017504420384360575617963)
        ·
          refine ⟨111026256630576540863426945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74017504420384360575617963 111026256630576540863426945)
          ·
            refine ⟨83269692472932405647570209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111026256630576540863426945 83269692472932405647570209)
            ·
              refine ⟨62452269354699304235677657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83269692472932405647570209 62452269354699304235677657)
              ·
                refine ⟨46839202016024478176758243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62452269354699304235677657 46839202016024478176758243)
                ·
                  refine ⟨70258803024036717265137365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46839202016024478176758243 70258803024036717265137365)
                  ·
                    refine ⟨1646690695875860560901657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70258803024036717265137365 1646690695875860560901657)
                    ·
                      refine ⟨1235018021906895420676243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646690695875860560901657 1235018021906895420676243)
                      ·
                        rfl

theorem cell23_2405189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_2405189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405189 prefixEnd_2405189 := by exact prefixLift 2405189
  have htrace : WordTrace (prefixWord ++ tailWord_2405189) baseStart_2405189 baseEnd_2405189 := by
    simpa [prefixWord, tailWord_2405189, baseEnd_2405189] using wordTrace_append hprefix tailTrace_2405189
  have hstable : (prefixWord ++ tailWord_2405189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405189).length < 2 ^ (prefixWord ++ tailWord_2405189).sum := by decide
  have hdescent : baseEnd_2405189 < baseStart_2405189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405219 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2405219 : Nat := 118140960795 + 2405219 * 2 ^ 59
def prefixEnd_2405219 : Nat := 4983230072969 + 3 ^ 40 * 2405219 * 2
def baseEnd_2405219 : Nat := 1235033426326530303301105

theorem tailTrace_2405219 : CollatzResearch.WordTrace tailWord_2405219 prefixEnd_2405219 1235033426326530303301105 := by
  unfold tailWord_2405219
  simp only [CollatzResearch.WordTrace]
  refine ⟨87725543873309816546546711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58483695915539877697697807 87725543873309816546546711)
  ·
    refine ⟨131588315809964724819820067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87725543873309816546546711 131588315809964724819820067)
    ·
      refine ⟨197382473714947087229730101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131588315809964724819820067 197382473714947087229730101)
      ·
        refine ⟨18504606910776289427787197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197382473714947087229730101 18504606910776289427787197)
        ·
          refine ⟨6939227591541108535420199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18504606910776289427787197 6939227591541108535420199)
          ·
            refine ⟨10408841387311662803130299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939227591541108535420199 10408841387311662803130299)
            ·
              refine ⟨15613262080967494204695449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10408841387311662803130299 15613262080967494204695449)
              ·
                refine ⟨11709946560725620653521587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15613262080967494204695449 11709946560725620653521587)
                ·
                  refine ⟨17564919841088430980282381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11709946560725620653521587 17564919841088430980282381)
                  ·
                    refine ⟨6586844940408161617605893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17564919841088430980282381 6586844940408161617605893)
                    ·
                      refine ⟨1235033426326530303301105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6586844940408161617605893 1235033426326530303301105)
                      ·
                        rfl

theorem cell23_2405219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2405219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405219 prefixEnd_2405219 := by exact prefixLift 2405219
  have htrace : WordTrace (prefixWord ++ tailWord_2405219) baseStart_2405219 baseEnd_2405219 := by
    simpa [prefixWord, tailWord_2405219, baseEnd_2405219] using wordTrace_append hprefix tailTrace_2405219
  have hstable : (prefixWord ++ tailWord_2405219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405219).length < 2 ^ (prefixWord ++ tailWord_2405219).sum := by decide
  have hdescent : baseEnd_2405219 < baseStart_2405219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405239 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_2405239 : Nat := 118140960795 + 2405239 * 2 ^ 59
def prefixEnd_2405239 : Nat := 4983230072969 + 3 ^ 40 * 2405239 * 2
def baseEnd_2405239 : Nat := 1235043695939620225051013

theorem tailTrace_2405239 : CollatzResearch.WordTrace tailWord_2405239 prefixEnd_2405239 1235043695939620225051013 := by
  unfold tailWord_2405239
  simp only [CollatzResearch.WordTrace]
  refine ⟨87726273333237359962274771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58484182222158239974849847 87726273333237359962274771)
  ·
    refine ⟨131589409999856039943412157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87726273333237359962274771 131589409999856039943412157)
    ·
      refine ⟨49346028749946014978779559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131589409999856039943412157 49346028749946014978779559)
      ·
        refine ⟨74019043124919022468169339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49346028749946014978779559 74019043124919022468169339)
        ·
          refine ⟨111028564687378533702254009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74019043124919022468169339 111028564687378533702254009)
          ·
            refine ⟨83271423515533900276690507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111028564687378533702254009 83271423515533900276690507)
            ·
              refine ⟨124907135273300850415035761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83271423515533900276690507 124907135273300850415035761)
              ·
                refine ⟨93680351454975637811276821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124907135273300850415035761 93680351454975637811276821)
                ·
                  refine ⟨4391266474451983022403601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93680351454975637811276821 4391266474451983022403601)
                  ·
                    refine ⟨3293449855838987266802701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4391266474451983022403601 3293449855838987266802701)
                    ·
                      refine ⟨1235043695939620225051013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3293449855838987266802701 1235043695939620225051013)
                      ·
                        rfl

theorem cell23_2405239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_2405239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405239 prefixEnd_2405239 := by exact prefixLift 2405239
  have htrace : WordTrace (prefixWord ++ tailWord_2405239) baseStart_2405239 baseEnd_2405239 := by
    simpa [prefixWord, tailWord_2405239, baseEnd_2405239] using wordTrace_append hprefix tailTrace_2405239
  have hstable : (prefixWord ++ tailWord_2405239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405239).length < 2 ^ (prefixWord ++ tailWord_2405239).sum := by decide
  have hdescent : baseEnd_2405239 < baseStart_2405239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405250 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2405250 : Nat := 118140960795 + 2405250 * 2 ^ 59
def prefixEnd_2405250 : Nat := 4983230072969 + 3 ^ 40 * 2405250 * 2
def baseEnd_2405250 : Nat := 411683114742273227337821

theorem tailTrace_2405250 : CollatzResearch.WordTrace tailWord_2405250 prefixEnd_2405250 411683114742273227337821 := by
  unfold tailWord_2405250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21931668634049377210231301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58484449690798339227283469 21931668634049377210231301)
  ·
    refine ⟨4112187868884258226918369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21931668634049377210231301 4112187868884258226918369)
    ·
      refine ⟨3084140901663193670188777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4112187868884258226918369 3084140901663193670188777)
      ·
        refine ⟨2313105676247395252641583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3084140901663193670188777 2313105676247395252641583)
        ·
          refine ⟨3469658514371092878962375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313105676247395252641583 3469658514371092878962375)
          ·
            refine ⟨5204487771556639318443563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469658514371092878962375 5204487771556639318443563)
            ·
              refine ⟨7806731657334958977665345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204487771556639318443563 7806731657334958977665345)
              ·
                refine ⟨5855048743001219233249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7806731657334958977665345 5855048743001219233249009)
                ·
                  refine ⟨4391286557250914424936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855048743001219233249009 4391286557250914424936757)
                  ·
                    refine ⟨411683114742273227337821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4391286557250914424936757 411683114742273227337821)
                    ·
                      rfl

theorem cell23_2405250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2405250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405250 prefixEnd_2405250 := by exact prefixLift 2405250
  have htrace : WordTrace (prefixWord ++ tailWord_2405250) baseStart_2405250 baseEnd_2405250 := by
    simpa [prefixWord, tailWord_2405250, baseEnd_2405250] using wordTrace_append hprefix tailTrace_2405250
  have hstable : (prefixWord ++ tailWord_2405250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405250).length < 2 ^ (prefixWord ++ tailWord_2405250).sum := by decide
  have hdescent : baseEnd_2405250 < baseStart_2405250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405256 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2405256 : Nat := 118140960795 + 2405256 * 2 ^ 59
def prefixEnd_2405256 : Nat := 4983230072969 + 3 ^ 40 * 2405256 * 2
def baseEnd_2405256 : Nat := 1235052425110746658538435

theorem tailTrace_2405256 : CollatzResearch.WordTrace tailWord_2405256 prefixEnd_2405256 1235052425110746658538435 := by
  unfold tailWord_2405256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43863446687087885932821811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58484595582783847910429081 43863446687087885932821811)
  ·
    refine ⟨65795170030631828899232717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43863446687087885932821811 65795170030631828899232717)
    ·
      refine ⟨24673188761486935837212269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65795170030631828899232717 24673188761486935837212269)
      ·
        refine ⟨9252445785557600938954601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24673188761486935837212269 9252445785557600938954601)
        ·
          refine ⟨6939334339168200704215951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252445785557600938954601 6939334339168200704215951)
          ·
            refine ⟨10409001508752301056323927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939334339168200704215951 10409001508752301056323927)
            ·
              refine ⟨15613502263128451584485891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409001508752301056323927 15613502263128451584485891)
              ·
                refine ⟨23420253394692677376728837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15613502263128451584485891 23420253394692677376728837)
                ·
                  refine ⟨4391297511504877008136657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23420253394692677376728837 4391297511504877008136657)
                  ·
                    refine ⟨3293473133628657756102493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4391297511504877008136657 3293473133628657756102493)
                    ·
                      refine ⟨1235052425110746658538435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3293473133628657756102493 1235052425110746658538435)
                      ·
                        rfl

theorem cell23_2405256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2405256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405256 prefixEnd_2405256 := by exact prefixLift 2405256
  have htrace : WordTrace (prefixWord ++ tailWord_2405256) baseStart_2405256 baseEnd_2405256 := by
    simpa [prefixWord, tailWord_2405256, baseEnd_2405256] using wordTrace_append hprefix tailTrace_2405256
  have hstable : (prefixWord ++ tailWord_2405256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405256).length < 2 ^ (prefixWord ++ tailWord_2405256).sum := by decide
  have hdescent : baseEnd_2405256 < baseStart_2405256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405289 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_2405289 : Nat := 118140960795 + 2405289 * 2 ^ 59
def prefixEnd_2405289 : Nat := 4983230072969 + 3 ^ 40 * 2405289 * 2
def baseEnd_2405289 : Nat := 411689789990781676475261

theorem tailTrace_2405289 : CollatzResearch.WordTrace tailWord_2405289 prefixEnd_2405289 411689789990781676475261 := by
  unfold tailWord_2405289
  simp only [CollatzResearch.WordTrace]
  refine ⟨87728096983056218501594921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58485397988704145667729947 87728096983056218501594921)
  ·
    refine ⟨65796072737292163876196191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87728096983056218501594921 65796072737292163876196191)
    ·
      refine ⟨98694109105938245814294287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65796072737292163876196191 98694109105938245814294287)
      ·
        refine ⟨148041163658907368721441431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98694109105938245814294287 148041163658907368721441431)
        ·
          refine ⟨222061745488361053082162147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148041163658907368721441431 222061745488361053082162147)
          ·
            refine ⟨333092618232541579623243221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222061745488361053082162147 333092618232541579623243221)
            ·
              refine ⟨7806858239825193272419763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 333092618232541579623243221 7806858239825193272419763)
              ·
                refine ⟨11710287359737789908629645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806858239825193272419763 11710287359737789908629645)
                ·
                  refine ⟨4391357759901671215736117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11710287359737789908629645 4391357759901671215736117)
                  ·
                    refine ⟨411689789990781676475261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4391357759901671215736117 411689789990781676475261)
                    ·
                      rfl

theorem cell23_2405289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_2405289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405289 prefixEnd_2405289 := by exact prefixLift 2405289
  have htrace : WordTrace (prefixWord ++ tailWord_2405289) baseStart_2405289 baseEnd_2405289 := by
    simpa [prefixWord, tailWord_2405289, baseEnd_2405289] using wordTrace_append hprefix tailTrace_2405289
  have hstable : (prefixWord ++ tailWord_2405289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405289).length < 2 ^ (prefixWord ++ tailWord_2405289).sum := by decide
  have hdescent : baseEnd_2405289 < baseStart_2405289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405326 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2405326 : Nat := 118140960795 + 2405326 * 2 ^ 59
def prefixEnd_2405326 : Nat := 4983230072969 + 3 ^ 40 * 2405326 * 2
def baseEnd_2405326 : Nat := 1235088368756561384663113

theorem tailTrace_2405326 : CollatzResearch.WordTrace tailWord_2405326 prefixEnd_2405326 1235088368756561384663113 := by
  unfold tailWord_2405326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966180810490271727586479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58486297655948115880461221 10966180810490271727586479)
  ·
    refine ⟨16449271215735407591379719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10966180810490271727586479 16449271215735407591379719)
    ·
      refine ⟨24673906823603111387069579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16449271215735407591379719 24673906823603111387069579)
      ·
        refine ⟨37010860235404667080604369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24673906823603111387069579 37010860235404667080604369)
        ·
          refine ⟨27758145176553500310453277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37010860235404667080604369 27758145176553500310453277)
          ·
            refine ⟨10409304441207562616419979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27758145176553500310453277 10409304441207562616419979)
            ·
              refine ⟨15613956661811343924629969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409304441207562616419979 15613956661811343924629969)
              ·
                refine ⟨11710467496358507943472477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15613956661811343924629969 11710467496358507943472477)
                ·
                  refine ⟨4391425311134440478802179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11710467496358507943472477 4391425311134440478802179)
                  ·
                    refine ⟨6587137966701660718203269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391425311134440478802179 6587137966701660718203269)
                    ·
                      refine ⟨1235088368756561384663113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6587137966701660718203269 1235088368756561384663113)
                      ·
                        rfl

theorem cell23_2405326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2405326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405326 prefixEnd_2405326 := by exact prefixLift 2405326
  have htrace : WordTrace (prefixWord ++ tailWord_2405326) baseStart_2405326 baseEnd_2405326 := by
    simpa [prefixWord, tailWord_2405326, baseEnd_2405326] using wordTrace_append hprefix tailTrace_2405326
  have hstable : (prefixWord ++ tailWord_2405326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405326).length < 2 ^ (prefixWord ++ tailWord_2405326).sum := by decide
  have hdescent : baseEnd_2405326 < baseStart_2405326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405329 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_2405329 : Nat := 118140960795 + 2405329 * 2 ^ 59
def prefixEnd_2405329 : Nat := 4983230072969 + 3 ^ 40 * 2405329 * 2
def baseEnd_2405329 : Nat := 1235089909198524872925599

theorem tailTrace_2405329 : CollatzResearch.WordTrace tailWord_2405329 prefixEnd_2405329 1235089909198524872925599 := by
  unfold tailWord_2405329
  simp only [CollatzResearch.WordTrace]
  refine ⟨87729555902911305333051041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58486370601940870222034027 87729555902911305333051041)
  ·
    refine ⟨65797166927183478999788281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87729555902911305333051041 65797166927183478999788281)
    ·
      refine ⟨49347875195387609249841211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65797166927183478999788281 49347875195387609249841211)
      ·
        refine ⟨74021812793081413874761817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49347875195387609249841211 74021812793081413874761817)
        ·
          refine ⟨55516359594811060406071363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74021812793081413874761817 55516359594811060406071363)
          ·
            refine ⟨83274539392216590609107045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55516359594811060406071363 83274539392216590609107045)
            ·
              refine ⟨15613976136040610739207571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83274539392216590609107045 15613976136040610739207571)
              ·
                refine ⟨23420964204060916108811357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15613976136040610739207571 23420964204060916108811357)
                ·
                  refine ⟨8782861576522843540804259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23420964204060916108811357 8782861576522843540804259)
                  ·
                    refine ⟨13174292364784265311206389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8782861576522843540804259 13174292364784265311206389)
                    ·
                      refine ⟨1235089909198524872925599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13174292364784265311206389 1235089909198524872925599)
                      ·
                        rfl

theorem cell23_2405329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_2405329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405329 prefixEnd_2405329 := by exact prefixLift 2405329
  have htrace : WordTrace (prefixWord ++ tailWord_2405329) baseStart_2405329 baseEnd_2405329 := by
    simpa [prefixWord, tailWord_2405329, baseEnd_2405329] using wordTrace_append hprefix tailTrace_2405329
  have hstable : (prefixWord ++ tailWord_2405329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405329).length < 2 ^ (prefixWord ++ tailWord_2405329).sum := by decide
  have hdescent : baseEnd_2405329 < baseStart_2405329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405336 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_2405336 : Nat := 118140960795 + 2405336 * 2 ^ 59
def prefixEnd_2405336 : Nat := 4983230072969 + 3 ^ 40 * 2405336 * 2
def baseEnd_2405336 : Nat := 411697834521035448512689

theorem tailTrace_2405336 : CollatzResearch.WordTrace tailWord_2405336 prefixEnd_2405336 411697834521035448512689 := by
  unfold tailWord_2405336
  simp only [CollatzResearch.WordTrace]
  refine ⟨43864905606942972764277931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58486540809257297019037241 43864905606942972764277931)
  ·
    refine ⟨65797358410414459146416897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43864905606942972764277931 65797358410414459146416897)
    ·
      refine ⟨49348018807810844359812673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65797358410414459146416897 49348018807810844359812673)
      ·
        refine ⟨37011014105858133269859505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49348018807810844359812673 37011014105858133269859505)
        ·
          refine ⟨27758260579393599952394629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37011014105858133269859505 27758260579393599952394629)
          ·
            refine ⟨5204673858636299991073993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27758260579393599952394629 5204673858636299991073993)
            ·
              refine ⟨3903505393977224993305495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5204673858636299991073993 3903505393977224993305495)
              ·
                refine ⟨5855258090965837489958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903505393977224993305495 5855258090965837489958243)
                ·
                  refine ⟨8782887136448756234937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855258090965837489958243 8782887136448756234937365)
                  ·
                    refine ⟨411697834521035448512689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8782887136448756234937365 411697834521035448512689)
                    ·
                      rfl

theorem cell23_2405336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_2405336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405336 prefixEnd_2405336 := by exact prefixLift 2405336
  have htrace : WordTrace (prefixWord ++ tailWord_2405336) baseStart_2405336 baseEnd_2405336 := by
    simpa [prefixWord, tailWord_2405336, baseEnd_2405336] using wordTrace_append hprefix tailTrace_2405336
  have hstable : (prefixWord ++ tailWord_2405336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405336).length < 2 ^ (prefixWord ++ tailWord_2405336).sum := by decide
  have hdescent : baseEnd_2405336 < baseStart_2405336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405366 : List Nat := [5, 1, 1, 1, 3, 2, 10]
def baseStart_2405366 : Nat := 118140960795 + 2405366 * 2 ^ 59
def prefixEnd_2405366 : Nat := 4983230072969 + 3 ^ 40 * 2405366 * 2
def baseEnd_2405366 : Nat := 15248258123243718866209

theorem tailTrace_2405366 : CollatzResearch.WordTrace tailWord_2405366 prefixEnd_2405366 15248258123243718866209 := by
  unfold tailWord_2405366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483181587736078790759247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58487270269184840434765301 5483181587736078790759247)
  ·
    refine ⟨8224772381604118186138871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5483181587736078790759247 8224772381604118186138871)
    ·
      refine ⟨12337158572406177279208307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8224772381604118186138871 12337158572406177279208307)
      ·
        refine ⟨18505737858609265918812461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12337158572406177279208307 18505737858609265918812461)
        ·
          refine ⟨6939651696978474719554673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18505737858609265918812461 6939651696978474719554673)
          ·
            refine ⟨5204738772733856039666005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6939651696978474719554673 5204738772733856039666005)
            ·
              refine ⟨15248258123243718866209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5204738772733856039666005 15248258123243718866209)
              ·
                rfl

theorem cell23_2405366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 10].length) (baseStart_2405366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405366 prefixEnd_2405366 := by exact prefixLift 2405366
  have htrace : WordTrace (prefixWord ++ tailWord_2405366) baseStart_2405366 baseEnd_2405366 := by
    simpa [prefixWord, tailWord_2405366, baseEnd_2405366] using wordTrace_append hprefix tailTrace_2405366
  have hstable : (prefixWord ++ tailWord_2405366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405366).length < 2 ^ (prefixWord ++ tailWord_2405366).sum := by decide
  have hdescent : baseEnd_2405366 < baseStart_2405366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405377 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_2405377 : Nat := 118140960795 + 2405377 * 2 ^ 59
def prefixEnd_2405377 : Nat := 4983230072969 + 3 ^ 40 * 2405377 * 2
def baseEnd_2405377 : Nat := 1235114556269940685125379

theorem tailTrace_2405377 : CollatzResearch.WordTrace tailWord_2405377 prefixEnd_2405377 1235114556269940685125379 := by
  unfold tailWord_2405377
  simp only [CollatzResearch.WordTrace]
  refine ⟨87731306606737409530798385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58487537737824939687198923 87731306606737409530798385)
  ·
    refine ⟨65798479955053057148098789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87731306606737409530798385 65798479955053057148098789)
    ·
      refine ⟨12337214991572448215268523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65798479955053057148098789 12337214991572448215268523)
      ·
        refine ⟨18505822487358672322902785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12337214991572448215268523 18505822487358672322902785)
        ·
          refine ⟨13879366865519004242177089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18505822487358672322902785 13879366865519004242177089)
          ·
            refine ⟨10409525149139253181632817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13879366865519004242177089 10409525149139253181632817)
            ·
              refine ⟨7807143861854439886224613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10409525149139253181632817 7807143861854439886224613)
              ·
                refine ⟨1463839474097707478667115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7807143861854439886224613 1463839474097707478667115)
                ·
                  refine ⟨2195759211146561218000673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463839474097707478667115 2195759211146561218000673)
                  ·
                    refine ⟨1646819408359920913500505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195759211146561218000673 1646819408359920913500505)
                    ·
                      refine ⟨1235114556269940685125379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646819408359920913500505 1235114556269940685125379)
                      ·
                        rfl

theorem cell23_2405377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_2405377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405377 prefixEnd_2405377 := by exact prefixLift 2405377
  have htrace : WordTrace (prefixWord ++ tailWord_2405377) baseStart_2405377 baseEnd_2405377 := by
    simpa [prefixWord, tailWord_2405377, baseEnd_2405377] using wordTrace_append hprefix tailTrace_2405377
  have hstable : (prefixWord ++ tailWord_2405377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405377).length < 2 ^ (prefixWord ++ tailWord_2405377).sum := by decide
  have hdescent : baseEnd_2405377 < baseStart_2405377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405393 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_2405393 : Nat := 118140960795 + 2405393 * 2 ^ 59
def prefixEnd_2405393 : Nat := 4983230072969 + 3 ^ 40 * 2405393 * 2
def baseEnd_2405393 : Nat := 1235122771960412622525305

theorem tailTrace_2405393 : CollatzResearch.WordTrace tailWord_2405393 prefixEnd_2405393 1235122771960412622525305 := by
  unfold tailWord_2405393
  simp only [CollatzResearch.WordTrace]
  refine ⟨87731890174679444263380833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58487926783119629508920555 87731890174679444263380833)
  ·
    refine ⟨65798917631009583197535625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87731890174679444263380833 65798917631009583197535625)
    ·
      refine ⟨49349188223257187398151719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65798917631009583197535625 49349188223257187398151719)
      ·
        refine ⟨74023782334885781097227579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49349188223257187398151719 74023782334885781097227579)
        ·
          refine ⟨111035673502328671645841369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74023782334885781097227579 111035673502328671645841369)
          ·
            refine ⟨83276755126746503734381027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111035673502328671645841369 83276755126746503734381027)
            ·
              refine ⟨124915132690119755601571541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83276755126746503734381027 124915132690119755601571541)
              ·
                refine ⟨2927698422424681771911833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124915132690119755601571541 2927698422424681771911833)
                ·
                  refine ⟨2195773816818511328933875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2927698422424681771911833 2195773816818511328933875)
                  ·
                    refine ⟨3293660725227766993400813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195773816818511328933875 3293660725227766993400813)
                    ·
                      refine ⟨1235122771960412622525305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3293660725227766993400813 1235122771960412622525305)
                      ·
                        rfl

theorem cell23_2405393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_2405393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405393 prefixEnd_2405393 := by exact prefixLift 2405393
  have htrace : WordTrace (prefixWord ++ tailWord_2405393) baseStart_2405393 baseEnd_2405393 := by
    simpa [prefixWord, tailWord_2405393, baseEnd_2405393] using wordTrace_append hprefix tailTrace_2405393
  have hstable : (prefixWord ++ tailWord_2405393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405393).length < 2 ^ (prefixWord ++ tailWord_2405393).sum := by decide
  have hdescent : baseEnd_2405393 < baseStart_2405393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405394 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2405394 : Nat := 118140960795 + 2405394 * 2 ^ 59
def prefixEnd_2405394 : Nat := 4983230072969 + 3 ^ 40 * 2405394 * 2
def baseEnd_2405394 : Nat := 1235123285441067118612801

theorem tailTrace_2405394 : CollatzResearch.WordTrace tailWord_2405394 prefixEnd_2405394 1235123285441067118612801 := by
  unfold tailWord_2405394
  simp only [CollatzResearch.WordTrace]
  refine ⟨21932981661918955358541809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58487951098450547622778157 21932981661918955358541809)
  ·
    refine ⟨16449736246439216518906357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21932981661918955358541809 16449736246439216518906357)
    ·
      refine ⟨1542162773103676548647471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16449736246439216518906357 1542162773103676548647471)
      ·
        refine ⟨2313244159655514822971207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542162773103676548647471 2313244159655514822971207)
        ·
          refine ⟨3469866239483272234456811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313244159655514822971207 3469866239483272234456811)
          ·
            refine ⟨5204799359224908351685217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469866239483272234456811 5204799359224908351685217)
            ·
              refine ⟨3903599519418681263763913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5204799359224908351685217 3903599519418681263763913)
              ·
                refine ⟨2927699639564010947822935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903599519418681263763913 2927699639564010947822935)
                ·
                  refine ⟨4391549459346016421734403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927699639564010947822935 4391549459346016421734403)
                  ·
                    refine ⟨6587324189019024632601605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391549459346016421734403 6587324189019024632601605)
                    ·
                      refine ⟨1235123285441067118612801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6587324189019024632601605 1235123285441067118612801)
                      ·
                        rfl

theorem cell23_2405394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2405394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405394 prefixEnd_2405394 := by exact prefixLift 2405394
  have htrace : WordTrace (prefixWord ++ tailWord_2405394) baseStart_2405394 baseEnd_2405394 := by
    simpa [prefixWord, tailWord_2405394, baseEnd_2405394] using wordTrace_append hprefix tailTrace_2405394
  have hstable : (prefixWord ++ tailWord_2405394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405394).length < 2 ^ (prefixWord ++ tailWord_2405394).sum := by decide
  have hdescent : baseEnd_2405394 < baseStart_2405394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405453 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2405453 : Nat := 118140960795 + 2405453 * 2 ^ 59
def prefixEnd_2405453 : Nat := 4983230072969 + 3 ^ 40 * 2405453 * 2
def baseEnd_2405453 : Nat := 1235153580799682387775029

theorem tailTrace_2405453 : CollatzResearch.WordTrace tailWord_2405453 prefixEnd_2405453 1235153580799682387775029 := by
  unfold tailWord_2405453
  simp only [CollatzResearch.WordTrace]
  refine ⟨87734078554462074510565013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58489385702974716340376675 87734078554462074510565013)
  ·
    refine ⟨4112534932240409742682735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87734078554462074510565013 4112534932240409742682735)
    ·
      refine ⟨6168802398360614614024103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112534932240409742682735 6168802398360614614024103)
      ·
        refine ⟨9253203597540921921036155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168802398360614614024103 9253203597540921921036155)
        ·
          refine ⟨13879805396311382881554233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9253203597540921921036155 13879805396311382881554233)
          ·
            refine ⟨10409854047233537161165675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13879805396311382881554233 10409854047233537161165675)
            ·
              refine ⟨15614781070850305741748513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409854047233537161165675 15614781070850305741748513)
              ·
                refine ⟨11711085803137729306311385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15614781070850305741748513 11711085803137729306311385)
                ·
                  refine ⟨8783314352353296979733539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11711085803137729306311385 8783314352353296979733539)
                  ·
                    refine ⟨13174971528529945469600309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8783314352353296979733539 13174971528529945469600309)
                    ·
                      refine ⟨1235153580799682387775029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13174971528529945469600309 1235153580799682387775029)
                      ·
                        rfl

theorem cell23_2405453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2405453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405453 prefixEnd_2405453 := by exact prefixLift 2405453
  have htrace : WordTrace (prefixWord ++ tailWord_2405453) baseStart_2405453 baseEnd_2405453 := by
    simpa [prefixWord, tailWord_2405453, baseEnd_2405453] using wordTrace_append hprefix tailTrace_2405453
  have hstable : (prefixWord ++ tailWord_2405453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405453).length < 2 ^ (prefixWord ++ tailWord_2405453).sum := by decide
  have hdescent : baseEnd_2405453 < baseStart_2405453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405466 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2405466 : Nat := 118140960795 + 2405466 * 2 ^ 59
def prefixEnd_2405466 : Nat := 4983230072969 + 3 ^ 40 * 2405466 * 2
def baseEnd_2405466 : Nat := 1235160256048190836912469

theorem tailTrace_2405466 : CollatzResearch.WordTrace tailWord_2405466 prefixEnd_2405466 1235160256048190836912469 := by
  unfold tailWord_2405466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21933638175853744432697063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58489701802276651820525501 21933638175853744432697063)
  ·
    refine ⟨32900457263780616649045595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21933638175853744432697063 32900457263780616649045595)
    ·
      refine ⟨49350685895670924973568393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32900457263780616649045595 49350685895670924973568393)
      ·
        refine ⟨37013014421753193730176295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49350685895670924973568393 37013014421753193730176295)
        ·
          refine ⟨55519521632629790595264443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37013014421753193730176295 55519521632629790595264443)
          ·
            refine ⟨83279282448944685892896665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55519521632629790595264443 83279282448944685892896665)
            ·
              refine ⟨62459461836708514419672499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83279282448944685892896665 62459461836708514419672499)
              ·
                refine ⟨93689192755062771629508749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62459461836708514419672499 93689192755062771629508749)
                ·
                  refine ⟨35133447283148539361065781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93689192755062771629508749 35133447283148539361065781)
                  ·
                    refine ⟨3293760682795175565099917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35133447283148539361065781 3293760682795175565099917)
                    ·
                      refine ⟨1235160256048190836912469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3293760682795175565099917 1235160256048190836912469)
                      ·
                        rfl

theorem cell23_2405466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2405466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405466 prefixEnd_2405466 := by exact prefixLift 2405466
  have htrace : WordTrace (prefixWord ++ tailWord_2405466) baseStart_2405466 baseEnd_2405466 := by
    simpa [prefixWord, tailWord_2405466, baseEnd_2405466] using wordTrace_append hprefix tailTrace_2405466
  have hstable : (prefixWord ++ tailWord_2405466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405466).length < 2 ^ (prefixWord ++ tailWord_2405466).sum := by decide
  have hdescent : baseEnd_2405466 < baseStart_2405466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405496 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2405496 : Nat := 118140960795 + 2405496 * 2 ^ 59
def prefixEnd_2405496 : Nat := 4983230072969 + 3 ^ 40 * 2405496 * 2
def baseEnd_2405496 : Nat := 1235175660467825719537331

theorem tailTrace_2405496 : CollatzResearch.WordTrace tailWord_2405496 prefixEnd_2405496 1235175660467825719537331 := by
  unfold tailWord_2405496
  simp only [CollatzResearch.WordTrace]
  refine ⟨43867823446653146427190171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58490431262204195236253561 43867823446653146427190171)
  ·
    refine ⟨65801735169979719640785257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43867823446653146427190171 65801735169979719640785257)
    ·
      refine ⟨49351301377484789730588943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65801735169979719640785257 49351301377484789730588943)
      ·
        refine ⟨74026952066227184595883415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49351301377484789730588943 74026952066227184595883415)
        ·
          refine ⟨111040428099340776893825123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74026952066227184595883415 111040428099340776893825123)
          ·
            refine ⟨166560642149011165340737685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111040428099340776893825123 166560642149011165340737685)
            ·
              refine ⟨7807530100734898375347079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166560642149011165340737685 7807530100734898375347079)
              ·
                refine ⟨11711295151102347563020619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7807530100734898375347079 11711295151102347563020619)
                ·
                  refine ⟨17566942726653521344530929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11711295151102347563020619 17566942726653521344530929)
                  ·
                    refine ⟨13175207044990141008398197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17566942726653521344530929 13175207044990141008398197)
                    ·
                      refine ⟨1235175660467825719537331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13175207044990141008398197 1235175660467825719537331)
                      ·
                        rfl

theorem cell23_2405496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2405496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405496 prefixEnd_2405496 := by exact prefixLift 2405496
  have htrace : WordTrace (prefixWord ++ tailWord_2405496) baseStart_2405496 baseEnd_2405496 := by
    simpa [prefixWord, tailWord_2405496, baseEnd_2405496] using wordTrace_append hprefix tailTrace_2405496
  have hstable : (prefixWord ++ tailWord_2405496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405496).length < 2 ^ (prefixWord ++ tailWord_2405496).sum := by decide
  have hdescent : baseEnd_2405496 < baseStart_2405496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405523 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4]
def baseStart_2405523 : Nat := 118140960795 + 2405523 * 2 ^ 59
def prefixEnd_2405523 : Nat := 4983230072969 + 3 ^ 40 * 2405523 * 2
def baseEnd_2405523 : Nat := 1235189524445497113899707

theorem tailTrace_2405523 : CollatzResearch.WordTrace tailWord_2405523 prefixEnd_2405523 1235189524445497113899707 := by
  unfold tailWord_2405523
  simp only [CollatzResearch.WordTrace]
  refine ⟨87736631664208476465613223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58491087776138984310408815 87736631664208476465613223)
  ·
    refine ⟨131604947496312714698419835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87736631664208476465613223 131604947496312714698419835)
    ·
      refine ⟨197407421244469072047629753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131604947496312714698419835 197407421244469072047629753)
      ·
        refine ⟨148055565933351804035722315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197407421244469072047629753 148055565933351804035722315)
        ·
          refine ⟨222083348900027706053583473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148055565933351804035722315 222083348900027706053583473)
          ·
            refine ⟨166562511675020779540187605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222083348900027706053583473 166562511675020779540187605)
            ·
              refine ⟨3903808867383299520473147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166562511675020779540187605 3903808867383299520473147)
              ·
                refine ⟨5855713301074949280709721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903808867383299520473147 5855713301074949280709721)
                ·
                  refine ⟨4391784975806211960532291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855713301074949280709721 4391784975806211960532291)
                  ·
                    refine ⟨6587677463709317940798437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391784975806211960532291 6587677463709317940798437)
                    ·
                      refine ⟨1235189524445497113899707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6587677463709317940798437 1235189524445497113899707)
                      ·
                        rfl

theorem cell23_2405523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_2405523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405523 prefixEnd_2405523 := by exact prefixLift 2405523
  have htrace : WordTrace (prefixWord ++ tailWord_2405523) baseStart_2405523 baseEnd_2405523 := by
    simpa [prefixWord, tailWord_2405523, baseEnd_2405523] using wordTrace_append hprefix tailTrace_2405523
  have hstable : (prefixWord ++ tailWord_2405523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405523).length < 2 ^ (prefixWord ++ tailWord_2405523).sum := by decide
  have hdescent : baseEnd_2405523 < baseStart_2405523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405533 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2405533 : Nat := 118140960795 + 2405533 * 2 ^ 59
def prefixEnd_2405533 : Nat := 4983230072969 + 3 ^ 40 * 2405533 * 2
def baseEnd_2405533 : Nat := 411731553084014024924887

theorem tailTrace_2405533 : CollatzResearch.WordTrace tailWord_2405533 prefixEnd_2405533 411731553084014024924887 := by
  unfold tailWord_2405533
  simp only [CollatzResearch.WordTrace]
  refine ⟨87736996394172248173477253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58491330929448165448984835 87736996394172248173477253)
  ·
    refine ⟨16450686823907296532526985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87736996394172248173477253 16450686823907296532526985)
    ·
      refine ⟨12338015117930472399395239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16450686823907296532526985 12338015117930472399395239)
      ·
        refine ⟨18507022676895708599092859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12338015117930472399395239 18507022676895708599092859)
        ·
          refine ⟨27760534015343562898639289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18507022676895708599092859 27760534015343562898639289)
          ·
            refine ⟨20820400511507672173979467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27760534015343562898639289 20820400511507672173979467)
            ·
              refine ⟨31230600767261508260969201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20820400511507672173979467 31230600767261508260969201)
              ·
                refine ⟨23422950575446131195726901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31230600767261508260969201 23422950575446131195726901)
                ·
                  refine ⟨2195901616448074799599397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23422950575446131195726901 2195901616448074799599397)
                  ·
                    refine ⟨411731553084014024924887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195901616448074799599397 411731553084014024924887)
                    ·
                      rfl

theorem cell23_2405533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2405533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405533 prefixEnd_2405533 := by exact prefixLift 2405533
  have htrace : WordTrace (prefixWord ++ tailWord_2405533) baseStart_2405533 baseEnd_2405533 := by
    simpa [prefixWord, tailWord_2405533, baseEnd_2405533] using wordTrace_append hprefix tailTrace_2405533
  have hstable : (prefixWord ++ tailWord_2405533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405533).length < 2 ^ (prefixWord ++ tailWord_2405533).sum := by decide
  have hdescent : baseEnd_2405533 < baseStart_2405533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405536 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2405536 : Nat := 118140960795 + 2405536 * 2 ^ 59
def prefixEnd_2405536 : Nat := 4983230072969 + 3 ^ 40 * 2405536 * 2
def baseEnd_2405536 : Nat := 1235196199694005563037147

theorem tailTrace_2405536 : CollatzResearch.WordTrace tailWord_2405536 prefixEnd_2405536 1235196199694005563037147 := by
  unfold tailWord_2405536
  simp only [CollatzResearch.WordTrace]
  refine ⟨43868552906580689842918231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58491403875440919790557641 43868552906580689842918231)
  ·
    refine ⟨65802829359871034764377347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43868552906580689842918231 65802829359871034764377347)
    ·
      refine ⟨98704244039806552146566021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65802829359871034764377347 98704244039806552146566021)
      ·
        refine ⟨18507045757463728527481129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98704244039806552146566021 18507045757463728527481129)
        ·
          refine ⟨13880284318097796395610847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18507045757463728527481129 13880284318097796395610847)
          ·
            refine ⟨20820426477146694593416271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13880284318097796395610847 20820426477146694593416271)
            ·
              refine ⟨31230639715720041890124407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20820426477146694593416271 31230639715720041890124407)
              ·
                refine ⟨46845959573580062835186611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31230639715720041890124407 46845959573580062835186611)
                ·
                  refine ⟨70268939360370094252779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46845959573580062835186611 70268939360370094252779917)
                  ·
                    refine ⟨26350852260138785344792469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70268939360370094252779917 26350852260138785344792469)
                    ·
                      refine ⟨1235196199694005563037147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26350852260138785344792469 1235196199694005563037147)
                      ·
                        rfl

theorem cell23_2405536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2405536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405536 prefixEnd_2405536 := by exact prefixLift 2405536
  have htrace : WordTrace (prefixWord ++ tailWord_2405536) baseStart_2405536 baseEnd_2405536 := by
    simpa [prefixWord, tailWord_2405536, baseEnd_2405536] using wordTrace_append hprefix tailTrace_2405536
  have hstable : (prefixWord ++ tailWord_2405536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405536).length < 2 ^ (prefixWord ++ tailWord_2405536).sum := by decide
  have hdescent : baseEnd_2405536 < baseStart_2405536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405540 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_2405540 : Nat := 118140960795 + 2405540 * 2 ^ 59
def prefixEnd_2405540 : Nat := 4983230072969 + 3 ^ 40 * 2405540 * 2
def baseEnd_2405540 : Nat := 1235198253616623547387129

theorem tailTrace_2405540 : CollatzResearch.WordTrace tailWord_2405540 prefixEnd_2405540 1235198253616623547387129 := by
  unfold tailWord_2405540
  simp only [CollatzResearch.WordTrace]
  refine ⟨43868625852573444184491037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58491501136764592245988049 43868625852573444184491037)
  ·
    refine ⟨16450734694715041569184139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43868625852573444184491037 16450734694715041569184139)
    ·
      refine ⟨24676102042072562353776209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16450734694715041569184139 24676102042072562353776209)
      ·
        refine ⟨18507076531554421765332157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24676102042072562353776209 18507076531554421765332157)
        ·
          refine ⟨6940153699332908161999559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18507076531554421765332157 6940153699332908161999559)
          ·
            refine ⟨10410230548999362242999339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940153699332908161999559 10410230548999362242999339)
            ·
              refine ⟨15615345823499043364499009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410230548999362242999339 15615345823499043364499009)
              ·
                refine ⟨11711509367624282523374257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15615345823499043364499009 11711509367624282523374257)
                ·
                  refine ⟨8783632025718211892530693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11711509367624282523374257 8783632025718211892530693)
                  ·
                    refine ⟨1646931004822164729849505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8783632025718211892530693 1646931004822164729849505)
                    ·
                      refine ⟨1235198253616623547387129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646931004822164729849505 1235198253616623547387129)
                      ·
                        rfl

theorem cell23_2405540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_2405540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405540 prefixEnd_2405540 := by exact prefixLift 2405540
  have htrace : WordTrace (prefixWord ++ tailWord_2405540) baseStart_2405540 baseEnd_2405540 := by
    simpa [prefixWord, tailWord_2405540, baseEnd_2405540] using wordTrace_append hprefix tailTrace_2405540
  have hstable : (prefixWord ++ tailWord_2405540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405540).length < 2 ^ (prefixWord ++ tailWord_2405540).sum := by decide
  have hdescent : baseEnd_2405540 < baseStart_2405540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405600 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2]
def baseStart_2405600 : Nat := 118140960795 + 2405600 * 2 ^ 59
def prefixEnd_2405600 : Nat := 4983230072969 + 3 ^ 40 * 2405600 * 2
def baseEnd_2405600 : Nat := 1235229062455893312636853

theorem tailTrace_2405600 : CollatzResearch.WordTrace tailWord_2405600 prefixEnd_2405600 1235229062455893312636853 := by
  unfold tailWord_2405600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43869720042464759308083127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58492960056619679077444169 43869720042464759308083127)
  ·
    refine ⟨65804580063697138962124691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43869720042464759308083127 65804580063697138962124691)
    ·
      refine ⟨98706870095545708443187037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65804580063697138962124691 98706870095545708443187037)
      ·
        refine ⟨37015076285829640666195139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98706870095545708443187037 37015076285829640666195139)
        ·
          refine ⟨55522614428744460999292709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37015076285829640666195139 55522614428744460999292709)
          ·
            refine ⟨10410490205389586437367383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55522614428744460999292709 10410490205389586437367383)
            ·
              refine ⟨15615735308084379656051075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410490205389586437367383 15615735308084379656051075)
              ·
                refine ⟨23423602962126569484076613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615735308084379656051075 23423602962126569484076613)
                ·
                  refine ⟨4391925555398731778264365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23423602962126569484076613 4391925555398731778264365)
                  ·
                    refine ⟨1646972083274524416849137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4391925555398731778264365 1646972083274524416849137)
                    ·
                      refine ⟨1235229062455893312636853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1646972083274524416849137 1235229062455893312636853)
                      ·
                        rfl

theorem cell23_2405600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_2405600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405600 prefixEnd_2405600 := by exact prefixLift 2405600
  have htrace : WordTrace (prefixWord ++ tailWord_2405600) baseStart_2405600 baseEnd_2405600 := by
    simpa [prefixWord, tailWord_2405600, baseEnd_2405600] using wordTrace_append hprefix tailTrace_2405600
  have hstable : (prefixWord ++ tailWord_2405600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405600).length < 2 ^ (prefixWord ++ tailWord_2405600).sum := by decide
  have hdescent : baseEnd_2405600 < baseStart_2405600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405640 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_2405640 : Nat := 118140960795 + 2405640 * 2 ^ 59
def prefixEnd_2405640 : Nat := 4983230072969 + 3 ^ 40 * 2405640 * 2
def baseEnd_2405640 : Nat := 411749867227357718712223

theorem tailTrace_2405640 : CollatzResearch.WordTrace tailWord_2405640 prefixEnd_2405640 411749867227357718712223 := by
  unfold tailWord_2405640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870449502392302723811187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58493932669856403631748249 43870449502392302723811187)
  ·
    refine ⟨65805674253588454085716781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43870449502392302723811187 65805674253588454085716781)
    ·
      refine ⟨24677127845095670282143793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65805674253588454085716781 24677127845095670282143793)
      ·
        refine ⟨18507845883821752711607845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24677127845095670282143793 18507845883821752711607845)
        ·
          refine ⟨3470221103216578633426471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18507845883821752711607845 3470221103216578633426471)
          ·
            refine ⟨5205331654824867950139707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470221103216578633426471 5205331654824867950139707)
            ·
              refine ⟨7807997482237301925209561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205331654824867950139707 7807997482237301925209561)
              ·
                refine ⟨5855998111677976443907171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7807997482237301925209561 5855998111677976443907171)
                ·
                  refine ⟨8783997167516964665860757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855998111677976443907171 8783997167516964665860757)
                  ·
                    refine ⟨411749867227357718712223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8783997167516964665860757 411749867227357718712223)
                    ·
                      rfl

theorem cell23_2405640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_2405640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405640 prefixEnd_2405640 := by exact prefixLift 2405640
  have htrace : WordTrace (prefixWord ++ tailWord_2405640) baseStart_2405640 baseEnd_2405640 := by
    simpa [prefixWord, tailWord_2405640, baseEnd_2405640] using wordTrace_append hprefix tailTrace_2405640
  have hstable : (prefixWord ++ tailWord_2405640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405640).length < 2 ^ (prefixWord ++ tailWord_2405640).sum := by decide
  have hdescent : baseEnd_2405640 < baseStart_2405640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405643 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_2405643 : Nat := 118140960795 + 2405643 * 2 ^ 59
def prefixEnd_2405643 : Nat := 4983230072969 + 3 ^ 40 * 2405643 * 2
def baseEnd_2405643 : Nat := 1235251142124036644399155

theorem tailTrace_2405643 : CollatzResearch.WordTrace tailWord_2405643 prefixEnd_2405643 1235251142124036644399155 := by
  unfold tailWord_2405643
  simp only [CollatzResearch.WordTrace]
  refine ⟨87741008423773736959981583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58494005615849157973321055 87741008423773736959981583)
  ·
    refine ⟨131611512635660605439972375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87741008423773736959981583 131611512635660605439972375)
    ·
      refine ⟨197417268953490908159958563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131611512635660605439972375 197417268953490908159958563)
      ·
        refine ⟨296125903430236362239937845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197417268953490908159958563 296125903430236362239937845)
        ·
          refine ⟨27761803446584658959994173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 296125903430236362239937845 27761803446584658959994173)
          ·
            refine ⟨10410676292469247109997815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27761803446584658959994173 10410676292469247109997815)
            ·
              refine ⟨15616014438703870664996723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410676292469247109997815 15616014438703870664996723)
              ·
                refine ⟨23424021658055805997495085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15616014438703870664996723 23424021658055805997495085)
                ·
                  refine ⟨8784008121770927249060657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23424021658055805997495085 8784008121770927249060657)
                  ·
                    refine ⟨6588006091328195436795493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8784008121770927249060657 6588006091328195436795493)
                    ·
                      refine ⟨1235251142124036644399155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6588006091328195436795493 1235251142124036644399155)
                      ·
                        rfl

theorem cell23_2405643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_2405643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405643 prefixEnd_2405643 := by exact prefixLift 2405643
  have htrace : WordTrace (prefixWord ++ tailWord_2405643) baseStart_2405643 baseEnd_2405643 := by
    simpa [prefixWord, tailWord_2405643, baseEnd_2405643] using wordTrace_append hprefix tailTrace_2405643
  have hstable : (prefixWord ++ tailWord_2405643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405643).length < 2 ^ (prefixWord ++ tailWord_2405643).sum := by decide
  have hdescent : baseEnd_2405643 < baseStart_2405643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405677 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2405677 : Nat := 118140960795 + 2405677 * 2 ^ 59
def prefixEnd_2405677 : Nat := 4983230072969 + 3 ^ 40 * 2405677 * 2
def baseEnd_2405677 : Nat := 1235268600466289511373999

theorem tailTrace_2405677 : CollatzResearch.WordTrace tailWord_2405677 prefixEnd_2405677 1235268600466289511373999 := by
  unfold tailWord_2405677
  simp only [CollatzResearch.WordTrace]
  refine ⟨87742248505650560766719285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58494832337100373844479523 87742248505650560766719285)
  ·
    refine ⟨8225835797404740071879933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87742248505650560766719285 8225835797404740071879933)
    ·
      refine ⟨3084688424026777526954975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8225835797404740071879933 3084688424026777526954975)
      ·
        refine ⟨4627032636040166290432463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084688424026777526954975 4627032636040166290432463)
        ·
          refine ⟨6940548954060249435648695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627032636040166290432463 6940548954060249435648695)
          ·
            refine ⟨10410823431090374153473043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940548954060249435648695 10410823431090374153473043)
            ·
              refine ⟨15616235146635561230209565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410823431090374153473043 15616235146635561230209565)
              ·
                refine ⟨5856088179988335461328587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15616235146635561230209565 5856088179988335461328587)
                ·
                  refine ⟨8784132269982503191992881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856088179988335461328587 8784132269982503191992881)
                  ·
                    refine ⟨6588099202486877393994661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8784132269982503191992881 6588099202486877393994661)
                    ·
                      refine ⟨1235268600466289511373999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6588099202486877393994661 1235268600466289511373999)
                      ·
                        rfl

theorem cell23_2405677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2405677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405677 prefixEnd_2405677 := by exact prefixLift 2405677
  have htrace : WordTrace (prefixWord ++ tailWord_2405677) baseStart_2405677 baseEnd_2405677 := by
    simpa [prefixWord, tailWord_2405677, baseEnd_2405677] using wordTrace_append hprefix tailTrace_2405677
  have hstable : (prefixWord ++ tailWord_2405677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405677).length < 2 ^ (prefixWord ++ tailWord_2405677).sum := by decide
  have hdescent : baseEnd_2405677 < baseStart_2405677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405680 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_2405680 : Nat := 118140960795 + 2405680 * 2 ^ 59
def prefixEnd_2405680 : Nat := 4983230072969 + 3 ^ 40 * 2405680 * 2
def baseEnd_2405680 : Nat := 1235270140908252999636485

theorem tailTrace_2405680 : CollatzResearch.WordTrace tailWord_2405680 prefixEnd_2405680 1235270140908252999636485 := by
  unfold tailWord_2405680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43871178962319846139539247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58494905283093128186052329 43871178962319846139539247)
  ·
    refine ⟨65806768443479769209308871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43871178962319846139539247 65806768443479769209308871)
    ·
      refine ⟨98710152665219653813963307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65806768443479769209308871 98710152665219653813963307)
      ·
        refine ⟨148065228997829480720944961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98710152665219653813963307 148065228997829480720944961)
        ·
          refine ⟨111048921748372110540708721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148065228997829480720944961 111048921748372110540708721)
          ·
            refine ⟨83286691311279082905531541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111048921748372110540708721 83286691311279082905531541)
            ·
              refine ⟨3904063655216207011196791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83286691311279082905531541 3904063655216207011196791)
              ·
                refine ⟨5856095482824310516795187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904063655216207011196791 5856095482824310516795187)
                ·
                  refine ⟨8784143224236465775192781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856095482824310516795187 8784143224236465775192781)
                  ·
                    refine ⟨3294053709088674665697293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8784143224236465775192781 3294053709088674665697293)
                    ·
                      refine ⟨1235270140908252999636485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3294053709088674665697293 1235270140908252999636485)
                      ·
                        rfl

theorem cell23_2405680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_2405680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405680 prefixEnd_2405680 := by exact prefixLift 2405680
  have htrace : WordTrace (prefixWord ++ tailWord_2405680) baseStart_2405680 baseEnd_2405680 := by
    simpa [prefixWord, tailWord_2405680, baseEnd_2405680] using wordTrace_append hprefix tailTrace_2405680
  have hstable : (prefixWord ++ tailWord_2405680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405680).length < 2 ^ (prefixWord ++ tailWord_2405680).sum := by decide
  have hdescent : baseEnd_2405680 < baseStart_2405680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405697 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2405697 : Nat := 118140960795 + 2405697 * 2 ^ 59
def prefixEnd_2405697 : Nat := 4983230072969 + 3 ^ 40 * 2405697 * 2
def baseEnd_2405697 : Nat := 1235278870079379433123907

theorem tailTrace_2405697 : CollatzResearch.WordTrace tailWord_2405697 prefixEnd_2405697 1235278870079379433123907 := by
  unfold tailWord_2405697
  simp only [CollatzResearch.WordTrace]
  refine ⟨87742977965578104182447345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58495318643718736121631563 87742977965578104182447345)
  ·
    refine ⟨65807233474183578136835509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87742977965578104182447345 65807233474183578136835509)
    ·
      refine ⟨6169428138204710450328329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65807233474183578136835509 6169428138204710450328329)
      ·
        refine ⟨4627071103653532837746247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6169428138204710450328329 4627071103653532837746247)
        ·
          refine ⟨6940606655480299256619371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627071103653532837746247 6940606655480299256619371)
          ·
            refine ⟨10410909983220448884929057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940606655480299256619371 10410909983220448884929057)
            ·
              refine ⟨7808182487415336663696793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10410909983220448884929057 7808182487415336663696793)
              ·
                refine ⟨5856136865561502497772595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7808182487415336663696793 5856136865561502497772595)
                ·
                  refine ⟨8784205298342253746658893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856136865561502497772595 8784205298342253746658893)
                  ·
                    refine ⟨3294076986878345154997085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8784205298342253746658893 3294076986878345154997085)
                    ·
                      refine ⟨1235278870079379433123907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3294076986878345154997085 1235278870079379433123907)
                      ·
                        rfl

theorem cell23_2405697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2405697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405697 prefixEnd_2405697 := by exact prefixLift 2405697
  have htrace : WordTrace (prefixWord ++ tailWord_2405697) baseStart_2405697 baseEnd_2405697 := by
    simpa [prefixWord, tailWord_2405697, baseEnd_2405697] using wordTrace_append hprefix tailTrace_2405697
  have hstable : (prefixWord ++ tailWord_2405697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405697).length < 2 ^ (prefixWord ++ tailWord_2405697).sum := by decide
  have hdescent : baseEnd_2405697 < baseStart_2405697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405713 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_2405713 : Nat := 118140960795 + 2405713 * 2 ^ 59
def prefixEnd_2405713 : Nat := 4983230072969 + 3 ^ 40 * 2405713 * 2
def baseEnd_2405713 : Nat := 411762361923283790174611

theorem tailTrace_2405713 : CollatzResearch.WordTrace tailWord_2405713 prefixEnd_2405713 411762361923283790174611 := by
  unfold tailWord_2405713
  simp only [CollatzResearch.WordTrace]
  refine ⟨87743561533520138915029793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58495707689013425943353195 87743561533520138915029793)
  ·
    refine ⟨65807671150140104186272345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87743561533520138915029793 65807671150140104186272345)
    ·
      refine ⟨49355753362605078139704259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65807671150140104186272345 49355753362605078139704259)
      ·
        refine ⟨74033630043907617209556389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49355753362605078139704259 74033630043907617209556389)
        ·
          refine ⟨13881305633232678226791823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74033630043907617209556389 13881305633232678226791823)
          ·
            refine ⟨20821958449849017340187735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13881305633232678226791823 20821958449849017340187735)
            ·
              refine ⟨31232937674773526010281603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20821958449849017340187735 31232937674773526010281603)
              ·
                refine ⟨46849406512160289015422405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31232937674773526010281603 46849406512160289015422405)
                ·
                  refine ⟨8784263721030054190391701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46849406512160289015422405 8784263721030054190391701)
                  ·
                    refine ⟨411762361923283790174611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8784263721030054190391701 411762361923283790174611)
                    ·
                      rfl

theorem cell23_2405713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_2405713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405713 prefixEnd_2405713 := by exact prefixLift 2405713
  have htrace : WordTrace (prefixWord ++ tailWord_2405713) baseStart_2405713 baseEnd_2405713 := by
    simpa [prefixWord, tailWord_2405713, baseEnd_2405713] using wordTrace_append hprefix tailTrace_2405713
  have hstable : (prefixWord ++ tailWord_2405713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405713).length < 2 ^ (prefixWord ++ tailWord_2405713).sum := by decide
  have hdescent : baseEnd_2405713 < baseStart_2405713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405730 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2405730 : Nat := 118140960795 + 2405730 * 2 ^ 59
def prefixEnd_2405730 : Nat := 4983230072969 + 3 ^ 40 * 2405730 * 2
def baseEnd_2405730 : Nat := 411765271646992601337085

theorem tailTrace_2405730 : CollatzResearch.WordTrace tailWord_2405730 prefixEnd_2405730 411765271646992601337085 := by
  unfold tailWord_2405730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21936045393614637704599661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58496121049639033878932429 21936045393614637704599661)
  ·
    refine ⟨8226017022605489139224873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21936045393614637704599661 8226017022605489139224873)
    ·
      refine ⟨6169512766954116854418655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8226017022605489139224873 6169512766954116854418655)
      ·
        refine ⟨9254269150431175281627983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169512766954116854418655 9254269150431175281627983)
        ·
          refine ⟨13881403725646762922441975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9254269150431175281627983 13881403725646762922441975)
          ·
            refine ⟨20822105588470144383662963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13881403725646762922441975 20822105588470144383662963)
            ·
              refine ⟨31233158382705216575494445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20822105588470144383662963 31233158382705216575494445)
              ·
                refine ⟨11712434393514456215810417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31233158382705216575494445 11712434393514456215810417)
                ·
                  refine ⟨8784325795135842161857813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11712434393514456215810417 8784325795135842161857813)
                  ·
                    refine ⟨411765271646992601337085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8784325795135842161857813 411765271646992601337085)
                    ·
                      rfl

theorem cell23_2405730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2405730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405730 prefixEnd_2405730 := by exact prefixLift 2405730
  have htrace : WordTrace (prefixWord ++ tailWord_2405730) baseStart_2405730 baseEnd_2405730 := by
    simpa [prefixWord, tailWord_2405730, baseEnd_2405730] using wordTrace_append hprefix tailTrace_2405730
  have hstable : (prefixWord ++ tailWord_2405730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405730).length < 2 ^ (prefixWord ++ tailWord_2405730).sum := by decide
  have hdescent : baseEnd_2405730 < baseStart_2405730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405743 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 7]
def baseStart_2405743 : Nat := 118140960795 + 2405743 * 2 ^ 59
def prefixEnd_2405743 : Nat := 4983230072969 + 3 ^ 40 * 2405743 * 2
def baseEnd_2405743 : Nat := 137255832243276250349855

theorem tailTrace_2405743 : CollatzResearch.WordTrace tailWord_2405743 prefixEnd_2405743 137255832243276250349855 := by
  unfold tailWord_2405743
  simp only [CollatzResearch.WordTrace]
  refine ⟨87744655723411454038621883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58496437148940969359081255 87744655723411454038621883)
  ·
    refine ⟨131616983585117181057932825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87744655723411454038621883 131616983585117181057932825)
    ·
      refine ⟨98712737688837885793449619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131616983585117181057932825 98712737688837885793449619)
      ·
        refine ⟨148069106533256828690174429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98712737688837885793449619 148069106533256828690174429)
        ·
          refine ⟨55525914949971310758815411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148069106533256828690174429 55525914949971310758815411)
          ·
            refine ⟨83288872424956966138223117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55525914949971310758815411 83288872424956966138223117)
            ·
              refine ⟨31233327159358862301833669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83288872424956966138223117 31233327159358862301833669)
              ·
                refine ⟨5856248842379786681593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31233327159358862301833669 5856248842379786681593813)
                ·
                  refine ⟨137255832243276250349855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5856248842379786681593813 137255832243276250349855)
                  ·
                    rfl

theorem cell23_2405743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 7].length) (baseStart_2405743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405743 prefixEnd_2405743 := by exact prefixLift 2405743
  have htrace : WordTrace (prefixWord ++ tailWord_2405743) baseStart_2405743 baseEnd_2405743 := by
    simpa [prefixWord, tailWord_2405743, baseEnd_2405743] using wordTrace_append hprefix tailTrace_2405743
  have hstable : (prefixWord ++ tailWord_2405743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405743).length < 2 ^ (prefixWord ++ tailWord_2405743).sum := by decide
  have hdescent : baseEnd_2405743 < baseStart_2405743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405788 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2405788 : Nat := 118140960795 + 2405788 * 2 ^ 59
def prefixEnd_2405788 : Nat := 4983230072969 + 3 ^ 40 * 2405788 * 2
def baseEnd_2405788 : Nat := 1235325596818938577085989

theorem tailTrace_2405788 : CollatzResearch.WordTrace tailWord_2405788 prefixEnd_2405788 1235325596818938577085989 := by
  unfold tailWord_2405788
  simp only [CollatzResearch.WordTrace]
  refine ⟨43873148504124213362005009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58497531338832284482673345 43873148504124213362005009)
  ·
    refine ⟨32904861378093160021503757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43873148504124213362005009 32904861378093160021503757)
    ·
      refine ⟨12339323016784935008063909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32904861378093160021503757 12339323016784935008063909)
      ·
        refine ⟨2313623065647175314011983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12339323016784935008063909 2313623065647175314011983)
        ·
          refine ⟨3470434598470762971017975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313623065647175314011983 3470434598470762971017975)
          ·
            refine ⟨5205651897706144456526963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470434598470762971017975 5205651897706144456526963)
            ·
              refine ⟨7808477846559216684790445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205651897706144456526963 7808477846559216684790445)
              ·
                refine ⟨2928179192459706256796417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7808477846559216684790445 2928179192459706256796417)
                ·
                  refine ⟨2196134394344779692597313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2928179192459706256796417 2196134394344779692597313)
                  ·
                    refine ⟨1647100795758584769447985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196134394344779692597313 1647100795758584769447985)
                    ·
                      refine ⟨1235325596818938577085989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647100795758584769447985 1235325596818938577085989)
                      ·
                        rfl

theorem cell23_2405788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2405788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405788 prefixEnd_2405788 := by exact prefixLift 2405788
  have htrace : WordTrace (prefixWord ++ tailWord_2405788) baseStart_2405788 baseEnd_2405788 := by
    simpa [prefixWord, tailWord_2405788, baseEnd_2405788] using wordTrace_append hprefix tailTrace_2405788
  have hstable : (prefixWord ++ tailWord_2405788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405788).length < 2 ^ (prefixWord ++ tailWord_2405788).sum := by decide
  have hdescent : baseEnd_2405788 < baseStart_2405788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405937 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_2405937 : Nat := 118140960795 + 2405937 * 2 ^ 59
def prefixEnd_2405937 : Nat := 4983230072969 + 3 ^ 40 * 2405937 * 2
def baseEnd_2405937 : Nat := 1235402105436458494122803

theorem tailTrace_2405937 : CollatzResearch.WordTrace tailWord_2405937 prefixEnd_2405937 1235402105436458494122803 := by
  unfold tailWord_2405937
  simp only [CollatzResearch.WordTrace]
  refine ⟨87751731484708625171184065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58501154323139083447456043 87751731484708625171184065)
  ·
    refine ⟨65813798613531468878388049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87751731484708625171184065 65813798613531468878388049)
    ·
      refine ⟨49360348960148601658791037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65813798613531468878388049 49360348960148601658791037)
      ·
        refine ⟨18510130860055725622046639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49360348960148601658791037 18510130860055725622046639)
        ·
          refine ⟨27765196290083588433069959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18510130860055725622046639 27765196290083588433069959)
          ·
            refine ⟨41647794435125382649604939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27765196290083588433069959 41647794435125382649604939)
            ·
              refine ⟨62471691652688073974407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41647794435125382649604939 62471691652688073974407409)
              ·
                refine ⟨46853768739516055480805557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62471691652688073974407409 46853768739516055480805557)
                ·
                  refine ⟨4392540819329630201325521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46853768739516055480805557 4392540819329630201325521)
                  ·
                    refine ⟨3294405614497222650994141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4392540819329630201325521 3294405614497222650994141)
                    ·
                      refine ⟨1235402105436458494122803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3294405614497222650994141 1235402105436458494122803)
                      ·
                        rfl

theorem cell23_2405937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_2405937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405937 prefixEnd_2405937 := by exact prefixLift 2405937
  have htrace : WordTrace (prefixWord ++ tailWord_2405937) baseStart_2405937 baseEnd_2405937 := by
    simpa [prefixWord, tailWord_2405937, baseEnd_2405937] using wordTrace_append hprefix tailTrace_2405937
  have hstable : (prefixWord ++ tailWord_2405937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405937).length < 2 ^ (prefixWord ++ tailWord_2405937).sum := by decide
  have hdescent : baseEnd_2405937 < baseStart_2405937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405951 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 3, 2, 2]
def baseStart_2405951 : Nat := 118140960795 + 2405951 * 2 ^ 59
def prefixEnd_2405951 : Nat := 4983230072969 + 3 ^ 40 * 2405951 * 2
def baseEnd_2405951 : Nat := 1235409294165621439347739

theorem tailTrace_2405951 : CollatzResearch.WordTrace tailWord_2405951 prefixEnd_2405951 1235409294165621439347739 := by
  unfold tailWord_2405951
  simp only [CollatzResearch.WordTrace]
  refine ⟨87752242106657905562193707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58501494737771937041462471 87752242106657905562193707)
  ·
    refine ⟨131628363159986858343290561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87752242106657905562193707 131628363159986858343290561)
    ·
      refine ⟨98721272369990143757467921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131628363159986858343290561 98721272369990143757467921)
      ·
        refine ⟨74040954277492607818100941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98721272369990143757467921 74040954277492607818100941)
        ·
          refine ⟨27765357854059727931787853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74040954277492607818100941 27765357854059727931787853)
          ·
            refine ⟨10412009195272397974420445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27765357854059727931787853 10412009195272397974420445)
            ·
              refine ⟨3904503448227149240407667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10412009195272397974420445 3904503448227149240407667)
              ·
                refine ⟨5856755172340723860611501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904503448227149240407667 5856755172340723860611501)
                ·
                  refine ⟨2196283189627771447729313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5856755172340723860611501 2196283189627771447729313)
                  ·
                    refine ⟨1647212392220828585796985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196283189627771447729313 1647212392220828585796985)
                    ·
                      refine ⟨1235409294165621439347739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647212392220828585796985 1235409294165621439347739)
                      ·
                        rfl

theorem cell23_2405951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_2405951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405951 prefixEnd_2405951 := by exact prefixLift 2405951
  have htrace : WordTrace (prefixWord ++ tailWord_2405951) baseStart_2405951 baseEnd_2405951 := by
    simpa [prefixWord, tailWord_2405951, baseEnd_2405951] using wordTrace_append hprefix tailTrace_2405951
  have hstable : (prefixWord ++ tailWord_2405951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405951).length < 2 ^ (prefixWord ++ tailWord_2405951).sum := by decide
  have hdescent : baseEnd_2405951 < baseStart_2405951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2405967 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_2405967 : Nat := 118140960795 + 2405967 * 2 ^ 59
def prefixEnd_2405967 : Nat := 4983230072969 + 3 ^ 40 * 2405967 * 2
def baseEnd_2405967 : Nat := 1235417509856093376747665

theorem tailTrace_2405967 : CollatzResearch.WordTrace tailWord_2405967 prefixEnd_2405967 1235417509856093376747665 := by
  unfold tailWord_2405967
  simp only [CollatzResearch.WordTrace]
  refine ⟨87752825674599940294776155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58501883783066626863184103 87752825674599940294776155)
  ·
    refine ⟨131629238511899910442164233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87752825674599940294776155 131629238511899910442164233)
    ·
      refine ⟨98721928883924932831623175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131629238511899910442164233 98721928883924932831623175)
      ·
        refine ⟨148082893325887399247434763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98721928883924932831623175 148082893325887399247434763)
        ·
          refine ⟨222124339988831098871152145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148082893325887399247434763 222124339988831098871152145)
          ·
            refine ⟨166593254991623324153364109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222124339988831098871152145 166593254991623324153364109)
            ·
              refine ⟨62472470621858746557511541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166593254991623324153364109 62472470621858746557511541)
              ·
                refine ⟨5856794120799257489766707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62472470621858746557511541 5856794120799257489766707)
                ·
                  refine ⟨8785191181198886234650061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856794120799257489766707 8785191181198886234650061)
                  ·
                    refine ⟨3294446692949582337993773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8785191181198886234650061 3294446692949582337993773)
                    ·
                      refine ⟨1235417509856093376747665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3294446692949582337993773 1235417509856093376747665)
                      ·
                        rfl

theorem cell23_2405967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_2405967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2405967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2405967 prefixEnd_2405967 := by exact prefixLift 2405967
  have htrace : WordTrace (prefixWord ++ tailWord_2405967) baseStart_2405967 baseEnd_2405967 := by
    simpa [prefixWord, tailWord_2405967, baseEnd_2405967] using wordTrace_append hprefix tailTrace_2405967
  have hstable : (prefixWord ++ tailWord_2405967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2405967).length < 2 ^ (prefixWord ++ tailWord_2405967).sum := by decide
  have hdescent : baseEnd_2405967 < baseStart_2405967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2405967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406002 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_2406002 : Nat := 118140960795 + 2406002 * 2 ^ 59
def prefixEnd_2406002 : Nat := 4983230072969 + 3 ^ 40 * 2406002 * 2
def baseEnd_2406002 : Nat := 1235435481679000739810005

theorem tailTrace_2406002 : CollatzResearch.WordTrace tailWord_2406002 prefixEnd_2406002 1235435481679000739810005 := by
  unfold tailWord_2406002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21938525557368285318075065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58502734819648760848200173 21938525557368285318075065)
  ·
    refine ⟨16453894168026213988556299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21938525557368285318075065 16453894168026213988556299)
    ·
      refine ⟨24680841252039320982834449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16453894168026213988556299 24680841252039320982834449)
      ·
        refine ⟨18510630939029490737125837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24680841252039320982834449 18510630939029490737125837)
        ·
          refine ⟨6941486602136059026422189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18510630939029490737125837 6941486602136059026422189)
          ·
            refine ⟨2603057475801022134908321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6941486602136059026422189 2603057475801022134908321)
            ·
              refine ⟨1952293106850766601181241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603057475801022134908321 1952293106850766601181241)
              ·
                refine ⟨1464219830138074950885931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952293106850766601181241 1464219830138074950885931)
                ·
                  refine ⟨2196329745207112426328897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464219830138074950885931 2196329745207112426328897)
                  ·
                    refine ⟨1647247308905334319746673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196329745207112426328897 1647247308905334319746673)
                    ·
                      refine ⟨1235435481679000739810005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647247308905334319746673 1235435481679000739810005)
                      ·
                        rfl

theorem cell23_2406002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_2406002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406002 prefixEnd_2406002 := by exact prefixLift 2406002
  have htrace : WordTrace (prefixWord ++ tailWord_2406002) baseStart_2406002 baseEnd_2406002 := by
    simpa [prefixWord, tailWord_2406002, baseEnd_2406002] using wordTrace_append hprefix tailTrace_2406002
  have hstable : (prefixWord ++ tailWord_2406002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406002).length < 2 ^ (prefixWord ++ tailWord_2406002).sum := by decide
  have hdescent : baseEnd_2406002 < baseStart_2406002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406017 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2406017 : Nat := 118140960795 + 2406017 * 2 ^ 59
def prefixEnd_2406017 : Nat := 4983230072969 + 3 ^ 40 * 2406017 * 2
def baseEnd_2406017 : Nat := 411814394629606060374145

theorem tailTrace_2406017 : CollatzResearch.WordTrace tailWord_2406017 prefixEnd_2406017 411814394629606060374145 := by
  unfold tailWord_2406017
  simp only [CollatzResearch.WordTrace]
  refine ⟨87754649324418798834096305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58503099549612532556064203 87754649324418798834096305)
  ·
    refine ⟨65815986993314099125572229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87754649324418798834096305 65815986993314099125572229)
    ·
      refine ⟨12340497561246393586044793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65815986993314099125572229 12340497561246393586044793)
      ·
        refine ⟨9255373170934795189533595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12340497561246393586044793 9255373170934795189533595)
        ·
          refine ⟨13883059756402192784300393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255373170934795189533595 13883059756402192784300393)
          ·
            refine ⟨10412294817301644588225295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13883059756402192784300393 10412294817301644588225295)
            ·
              refine ⟨15618442225952466882337943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412294817301644588225295 15618442225952466882337943)
              ·
                refine ⟨23427663338928700323506915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15618442225952466882337943 23427663338928700323506915)
                ·
                  refine ⟨35141495008393050485260373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23427663338928700323506915 35141495008393050485260373)
                  ·
                    refine ⟨411814394629606060374145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35141495008393050485260373 411814394629606060374145)
                    ·
                      rfl

theorem cell23_2406017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2406017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406017 prefixEnd_2406017 := by exact prefixLift 2406017
  have htrace : WordTrace (prefixWord ++ tailWord_2406017) baseStart_2406017 baseEnd_2406017 := by
    simpa [prefixWord, tailWord_2406017, baseEnd_2406017] using wordTrace_append hprefix tailTrace_2406017
  have hstable : (prefixWord ++ tailWord_2406017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406017).length < 2 ^ (prefixWord ++ tailWord_2406017).sum := by decide
  have hdescent : baseEnd_2406017 < baseStart_2406017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406027 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3]
def baseStart_2406027 : Nat := 118140960795 + 2406027 * 2 ^ 59
def prefixEnd_2406027 : Nat := 4983230072969 + 3 ^ 40 * 2406027 * 2
def baseEnd_2406027 : Nat := 1235448318695363141997389

theorem tailTrace_2406027 : CollatzResearch.WordTrace tailWord_2406027 prefixEnd_2406027 1235448318695363141997389 := by
  unfold tailWord_2406027
  simp only [CollatzResearch.WordTrace]
  refine ⟨87755014054382570541960335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58503342702921713694640223 87755014054382570541960335)
  ·
    refine ⟨131632521081573855812940503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87755014054382570541960335 131632521081573855812940503)
    ·
      refine ⟨197448781622360783719410755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131632521081573855812940503 197448781622360783719410755)
      ·
        refine ⟨296173172433541175579116133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197448781622360783719410755 296173172433541175579116133)
        ·
          refine ⟨55532469831288970421084275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296173172433541175579116133 55532469831288970421084275)
          ·
            refine ⟨83298704746933455631626413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55532469831288970421084275 83298704746933455631626413)
            ·
              refine ⟨31237014280100045861859905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83298704746933455631626413 31237014280100045861859905)
              ·
                refine ⟨23427760710075034396394929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31237014280100045861859905 23427760710075034396394929)
                ·
                  refine ⟨17570820532556275797296197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23427760710075034396394929 17570820532556275797296197)
                  ·
                    refine ⟨3294528849854301711993037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17570820532556275797296197 3294528849854301711993037)
                    ·
                      refine ⟨1235448318695363141997389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3294528849854301711993037 1235448318695363141997389)
                      ·
                        rfl

theorem cell23_2406027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3].length) (baseStart_2406027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406027 prefixEnd_2406027 := by exact prefixLift 2406027
  have htrace : WordTrace (prefixWord ++ tailWord_2406027) baseStart_2406027 baseEnd_2406027 := by
    simpa [prefixWord, tailWord_2406027, baseEnd_2406027] using wordTrace_append hprefix tailTrace_2406027
  have hstable : (prefixWord ++ tailWord_2406027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406027).length < 2 ^ (prefixWord ++ tailWord_2406027).sum := by decide
  have hdescent : baseEnd_2406027 < baseStart_2406027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406064 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 5]
def baseStart_2406064 : Nat := 118140960795 + 2406064 * 2 ^ 59
def prefixEnd_2406064 : Nat := 4983230072969 + 3 ^ 40 * 2406064 * 2
def baseEnd_2406064 : Nat := 137274146386619944137191

theorem tailTrace_2406064 : CollatzResearch.WordTrace tailWord_2406064 prefixEnd_2406064 137274146386619944137191 := by
  unfold tailWord_2406064
  simp only [CollatzResearch.WordTrace]
  refine ⟨43878181777624262930528623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58504242370165683907371497 43878181777624262930528623)
  ·
    refine ⟨65817272666436394395792935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43878181777624262930528623 65817272666436394395792935)
    ·
      refine ⟨98725908999654591593689403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65817272666436394395792935 98725908999654591593689403)
      ·
        refine ⟨148088863499481887390534105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98725908999654591593689403 148088863499481887390534105)
        ·
          refine ⟨111066647624611415542900579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148088863499481887390534105 111066647624611415542900579)
          ·
            refine ⟨166599971436917123314350869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111066647624611415542900579 166599971436917123314350869)
            ·
              refine ⟨7809373661105490155360197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166599971436917123314350869 7809373661105490155360197)
              ·
                refine ⟨1464257561457279404130037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7809373661105490155360197 1464257561457279404130037)
                ·
                  refine ⟨137274146386619944137191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464257561457279404130037 137274146386619944137191)
                  ·
                    rfl

theorem cell23_2406064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 5].length) (baseStart_2406064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406064 prefixEnd_2406064 := by exact prefixLift 2406064
  have htrace : WordTrace (prefixWord ++ tailWord_2406064) baseStart_2406064 baseEnd_2406064 := by
    simpa [prefixWord, tailWord_2406064, baseEnd_2406064] using wordTrace_append hprefix tailTrace_2406064
  have hstable : (prefixWord ++ tailWord_2406064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406064).length < 2 ^ (prefixWord ++ tailWord_2406064).sum := by decide
  have hdescent : baseEnd_2406064 < baseStart_2406064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406074 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_2406074 : Nat := 118140960795 + 2406074 * 2 ^ 59
def prefixEnd_2406074 : Nat := 4983230072969 + 3 ^ 40 * 2406074 * 2
def baseEnd_2406074 : Nat := 1235472452286124458109673

theorem tailTrace_2406074 : CollatzResearch.WordTrace tailWord_2406074 prefixEnd_2406074 1235472452286124458109673 := by
  unfold tailWord_2406074
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939182071303074392230319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58504485523474865045947517 21939182071303074392230319)
  ·
    refine ⟨32908773106954611588345479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21939182071303074392230319 32908773106954611588345479)
    ·
      refine ⟨49363159660431917382518219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32908773106954611588345479 49363159660431917382518219)
      ·
        refine ⟨74044739490647876073777329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49363159660431917382518219 74044739490647876073777329)
        ·
          refine ⟨55533554617985907055332997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74044739490647876073777329 55533554617985907055332997)
          ·
            refine ⟨10412541490872357572874937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55533554617985907055332997 10412541490872357572874937)
            ·
              refine ⟨7809406118154268179656203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10412541490872357572874937 7809406118154268179656203)
              ·
                refine ⟨11714109177231402269484305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7809406118154268179656203 11714109177231402269484305)
                ·
                  refine ⟨8785581882923551702113229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11714109177231402269484305 8785581882923551702113229)
                  ·
                    refine ⟨3294593206096331888292461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8785581882923551702113229 3294593206096331888292461)
                    ·
                      refine ⟨1235472452286124458109673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3294593206096331888292461 1235472452286124458109673)
                      ·
                        rfl

theorem cell23_2406074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_2406074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406074 prefixEnd_2406074 := by exact prefixLift 2406074
  have htrace : WordTrace (prefixWord ++ tailWord_2406074) baseStart_2406074 baseEnd_2406074 := by
    simpa [prefixWord, tailWord_2406074, baseEnd_2406074] using wordTrace_append hprefix tailTrace_2406074
  have hstable : (prefixWord ++ tailWord_2406074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406074).length < 2 ^ (prefixWord ++ tailWord_2406074).sum := by decide
  have hdescent : baseEnd_2406074 < baseStart_2406074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406077 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2406077 : Nat := 118140960795 + 2406077 * 2 ^ 59
def prefixEnd_2406077 : Nat := 4983230072969 + 3 ^ 40 * 2406077 * 2
def baseEnd_2406077 : Nat := 411824664242695982124053

theorem tailTrace_2406077 : CollatzResearch.WordTrace tailWord_2406077 prefixEnd_2406077 411824664242695982124053 := by
  unfold tailWord_2406077
  simp only [CollatzResearch.WordTrace]
  refine ⟨87756837704201429081280485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58504558469467619387520323 87756837704201429081280485)
  ·
    refine ⟨16454407069537767952740091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87756837704201429081280485 16454407069537767952740091)
    ·
      refine ⟨24681610604306651929110137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16454407069537767952740091 24681610604306651929110137)
      ·
        refine ⟨18511207953229988946832603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24681610604306651929110137 18511207953229988946832603)
        ·
          refine ⟨27766811929844983420248905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18511207953229988946832603 27766811929844983420248905)
          ·
            refine ⟨20825108947383737565186679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27766811929844983420248905 20825108947383737565186679)
            ·
              refine ⟨31237663421075606347780019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20825108947383737565186679 31237663421075606347780019)
              ·
                refine ⟨46856495131613409521670029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31237663421075606347780019 46856495131613409521670029)
                ·
                  refine ⟨17571185674355028570626261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46856495131613409521670029 17571185674355028570626261)
                  ·
                    refine ⟨411824664242695982124053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17571185674355028570626261 411824664242695982124053)
                    ·
                      rfl

theorem cell23_2406077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2406077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406077 prefixEnd_2406077 := by exact prefixLift 2406077
  have htrace : WordTrace (prefixWord ++ tailWord_2406077) baseStart_2406077 baseEnd_2406077 := by
    simpa [prefixWord, tailWord_2406077, baseEnd_2406077] using wordTrace_append hprefix tailTrace_2406077
  have hstable : (prefixWord ++ tailWord_2406077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406077).length < 2 ^ (prefixWord ++ tailWord_2406077).sum := by decide
  have hdescent : baseEnd_2406077 < baseStart_2406077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406094 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2406094 : Nat := 118140960795 + 2406094 * 2 ^ 59
def prefixEnd_2406094 : Nat := 4983230072969 + 3 ^ 40 * 2406094 * 2
def baseEnd_2406094 : Nat := 411827573966404793286527

theorem tailTrace_2406094 : CollatzResearch.WordTrace tailWord_2406094 prefixEnd_2406094 411827573966404793286527 := by
  unfold tailWord_2406094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10969682218142480123081167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58504971830093227323099557 10969682218142480123081167)
  ·
    refine ⟨16454523327213720184621751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10969682218142480123081167 16454523327213720184621751)
    ·
      refine ⟨24681784990820580276932627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16454523327213720184621751 24681784990820580276932627)
      ·
        refine ⟨37022677486230870415398941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24681784990820580276932627 37022677486230870415398941)
        ·
          refine ⟨13883504057336576405774603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37022677486230870415398941 13883504057336576405774603)
          ·
            refine ⟨20825256086004864608661905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13883504057336576405774603 20825256086004864608661905)
            ·
              refine ⟨15618942064503648456496429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20825256086004864608661905 15618942064503648456496429)
              ·
                refine ⟨5857103274188868171186161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15618942064503648456496429 5857103274188868171186161)
                ·
                  refine ⟨4392827455641651128389621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857103274188868171186161 4392827455641651128389621)
                  ·
                    refine ⟨411827573966404793286527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4392827455641651128389621 411827573966404793286527)
                    ·
                      rfl

theorem cell23_2406094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2406094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406094 prefixEnd_2406094 := by exact prefixLift 2406094
  have htrace : WordTrace (prefixWord ++ tailWord_2406094) baseStart_2406094 baseEnd_2406094 := by
    simpa [prefixWord, tailWord_2406094, baseEnd_2406094] using wordTrace_append hprefix tailTrace_2406094
  have hstable : (prefixWord ++ tailWord_2406094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406094).length < 2 ^ (prefixWord ++ tailWord_2406094).sum := by decide
  have hdescent : baseEnd_2406094 < baseStart_2406094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406098 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_2406098 : Nat := 118140960795 + 2406098 * 2 ^ 59
def prefixEnd_2406098 : Nat := 4983230072969 + 3 ^ 40 * 2406098 * 2
def baseEnd_2406098 : Nat := 137276086202425818245507

theorem tailTrace_2406098 : CollatzResearch.WordTrace tailWord_2406098 prefixEnd_2406098 137276086202425818245507 := by
  unfold tailWord_2406098
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939400909281337416948737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58505069091416899778529965 21939400909281337416948737)
  ·
    refine ⟨16454550681961003062711553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21939400909281337416948737 16454550681961003062711553)
    ·
      refine ⟨12340913011470752297033665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16454550681961003062711553 12340913011470752297033665)
      ·
        refine ⟨9255684758603064222775249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12340913011470752297033665 9255684758603064222775249)
        ·
          refine ⟨6941763568952298167081437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9255684758603064222775249 6941763568952298167081437)
          ·
            refine ⟨2603161338357111812655539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6941763568952298167081437 2603161338357111812655539)
            ·
              refine ⟨3904742007535667718983309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603161338357111812655539 3904742007535667718983309)
              ·
                refine ⟨1464278252825875394618741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3904742007535667718983309 1464278252825875394618741)
                ·
                  refine ⟨137276086202425818245507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464278252825875394618741 137276086202425818245507)
                  ·
                    rfl

theorem cell23_2406098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_2406098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406098 prefixEnd_2406098 := by exact prefixLift 2406098
  have htrace : WordTrace (prefixWord ++ tailWord_2406098) baseStart_2406098 baseEnd_2406098 := by
    simpa [prefixWord, tailWord_2406098, baseEnd_2406098] using wordTrace_append hprefix tailTrace_2406098
  have hstable : (prefixWord ++ tailWord_2406098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406098).length < 2 ^ (prefixWord ++ tailWord_2406098).sum := by decide
  have hdescent : baseEnd_2406098 < baseStart_2406098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406224 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_2406224 : Nat := 118140960795 + 2406224 * 2 ^ 59
def prefixEnd_2406224 : Nat := 4983230072969 + 3 ^ 40 * 2406224 * 2
def baseEnd_2406224 : Nat := 1235549474384298871233983

theorem tailTrace_2406224 : CollatzResearch.WordTrace tailWord_2406224 prefixEnd_2406224 1235549474384298871233983 := by
  unfold tailWord_2406224
  simp only [CollatzResearch.WordTrace]
  refine ⟨43881099617334436593440863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58508132823112582124587817 43881099617334436593440863)
  ·
    refine ⟨65821649426001654890161295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43881099617334436593440863 65821649426001654890161295)
    ·
      refine ⟨98732474139002482335241943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65821649426001654890161295 98732474139002482335241943)
      ·
        refine ⟨148098711208503723502862915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98732474139002482335241943 148098711208503723502862915)
        ·
          refine ⟨222148066812755585254294373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148098711208503723502862915 222148066812755585254294373)
          ·
            refine ⟨41652762527391672235180195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222148066812755585254294373 41652762527391672235180195)
            ·
              refine ⟨62479143791087508352770293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41652762527391672235180195 62479143791087508352770293)
              ·
                refine ⟨5857419730414453908072215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62479143791087508352770293 5857419730414453908072215)
                ·
                  refine ⟨8786129595621680862108323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857419730414453908072215 8786129595621680862108323)
                  ·
                    refine ⟨13179194393432521293162485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8786129595621680862108323 13179194393432521293162485)
                    ·
                      refine ⟨1235549474384298871233983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13179194393432521293162485 1235549474384298871233983)
                      ·
                        rfl

theorem cell23_2406224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_2406224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406224 prefixEnd_2406224 := by exact prefixLift 2406224
  have htrace : WordTrace (prefixWord ++ tailWord_2406224) baseStart_2406224 baseEnd_2406224 := by
    simpa [prefixWord, tailWord_2406224, baseEnd_2406224] using wordTrace_append hprefix tailTrace_2406224
  have hstable : (prefixWord ++ tailWord_2406224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406224).length < 2 ^ (prefixWord ++ tailWord_2406224).sum := by decide
  have hdescent : baseEnd_2406224 < baseStart_2406224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406234 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2406234 : Nat := 118140960795 + 2406234 * 2 ^ 59
def prefixEnd_2406234 : Nat := 4983230072969 + 3 ^ 40 * 2406234 * 2
def baseEnd_2406234 : Nat := 1235554609190843832108937

theorem tailTrace_2406234 : CollatzResearch.WordTrace tailWord_2406234 prefixEnd_2406234 1235554609190843832108937 := by
  unfold tailWord_2406234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21940640991158161223686439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58508375976421763263163837 21940640991158161223686439)
  ·
    refine ⟨32910961486737241835529659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21940640991158161223686439 32910961486737241835529659)
    ·
      refine ⟨49366442230105862753294489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32910961486737241835529659 49366442230105862753294489)
      ·
        refine ⟨37024831672579397064970867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49366442230105862753294489 37024831672579397064970867)
        ·
          refine ⟨55537247508869095597456301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37024831672579397064970867 55537247508869095597456301)
          ·
            refine ⟨20826467815825910849046113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55537247508869095597456301 20826467815825910849046113)
            ·
              refine ⟨15619850861869433136784585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20826467815825910849046113 15619850861869433136784585)
              ·
                refine ⟨11714888146402074852588439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15619850861869433136784585 11714888146402074852588439)
                ·
                  refine ⟨17572332219603112278882659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11714888146402074852588439 17572332219603112278882659)
                  ·
                    refine ⟨26358498329404668418323989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17572332219603112278882659 26358498329404668418323989)
                    ·
                      refine ⟨1235554609190843832108937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26358498329404668418323989 1235554609190843832108937)
                      ·
                        rfl

theorem cell23_2406234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2406234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406234 prefixEnd_2406234 := by exact prefixLift 2406234
  have htrace : WordTrace (prefixWord ++ tailWord_2406234) baseStart_2406234 baseEnd_2406234 := by
    simpa [prefixWord, tailWord_2406234, baseEnd_2406234] using wordTrace_append hprefix tailTrace_2406234
  have hstable : (prefixWord ++ tailWord_2406234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406234).length < 2 ^ (prefixWord ++ tailWord_2406234).sum := by decide
  have hdescent : baseEnd_2406234 < baseStart_2406234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406284 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2406284 : Nat := 118140960795 + 2406284 * 2 ^ 59
def prefixEnd_2406284 : Nat := 4983230072969 + 3 ^ 40 * 2406284 * 2
def baseEnd_2406284 : Nat := 1235580283223568636483707

theorem tailTrace_2406284 : CollatzResearch.WordTrace tailWord_2406284 prefixEnd_2406284 1235580283223568636483707 := by
  unfold tailWord_2406284
  simp only [CollatzResearch.WordTrace]
  refine ⟨43882193807225751717032953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58509591742967668956043937 43882193807225751717032953)
  ·
    refine ⟨32911645355419313787774715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43882193807225751717032953 32911645355419313787774715)
    ·
      refine ⟨49367468033128970681662073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32911645355419313787774715 49367468033128970681662073)
      ·
        refine ⟨37025601024846728011246555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49367468033128970681662073 37025601024846728011246555)
        ·
          refine ⟨55538401537270092016869833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37025601024846728011246555 55538401537270092016869833)
          ·
            refine ⟨41653801152952569012652375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55538401537270092016869833 41653801152952569012652375)
            ·
              refine ⟨62480701729428853518978563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41653801152952569012652375 62480701729428853518978563)
              ·
                refine ⟨93721052594143280278467845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62480701729428853518978563 93721052594143280278467845)
                ·
                  refine ⟨17572697361401865052212721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93721052594143280278467845 17572697361401865052212721)
                  ·
                    refine ⟨13179523021051398789159541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17572697361401865052212721 13179523021051398789159541)
                    ·
                      refine ⟨1235580283223568636483707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13179523021051398789159541 1235580283223568636483707)
                      ·
                        rfl

theorem cell23_2406284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2406284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406284 prefixEnd_2406284 := by exact prefixLift 2406284
  have htrace : WordTrace (prefixWord ++ tailWord_2406284) baseStart_2406284 baseEnd_2406284 := by
    simpa [prefixWord, tailWord_2406284, baseEnd_2406284] using wordTrace_append hprefix tailTrace_2406284
  have hstable : (prefixWord ++ tailWord_2406284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406284).length < 2 ^ (prefixWord ++ tailWord_2406284).sum := by decide
  have hdescent : baseEnd_2406284 < baseStart_2406284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406304 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_2406304 : Nat := 118140960795 + 2406304 * 2 ^ 59
def prefixEnd_2406304 : Nat := 4983230072969 + 3 ^ 40 * 2406304 * 2
def baseEnd_2406304 : Nat := 411863517612219519411205

theorem tailTrace_2406304 : CollatzResearch.WordTrace tailWord_2406304 prefixEnd_2406304 411863517612219519411205 := by
  unfold tailWord_2406304
  simp only [CollatzResearch.WordTrace]
  refine ⟨43882558537189523424896983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58510078049586031233195977 43882558537189523424896983)
  ·
    refine ⟨65823837805784285137345475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43882558537189523424896983 65823837805784285137345475)
    ·
      refine ⟨98735756708676427706018213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65823837805784285137345475 98735756708676427706018213)
      ·
        refine ⟨18512954382876830194878415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98735756708676427706018213 18512954382876830194878415)
        ·
          refine ⟨27769431574315245292317623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18512954382876830194878415 27769431574315245292317623)
          ·
            refine ⟨41654147361472867938476435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27769431574315245292317623 41654147361472867938476435)
            ·
              refine ⟨62481221042209301907714653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41654147361472867938476435 62481221042209301907714653)
              ·
                refine ⟨23430457890828488215392995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62481221042209301907714653 23430457890828488215392995)
                ·
                  refine ⟨35145686836242732323089493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23430457890828488215392995 35145686836242732323089493)
                  ·
                    refine ⟨411863517612219519411205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35145686836242732323089493 411863517612219519411205)
                    ·
                      rfl

theorem cell23_2406304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_2406304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406304 prefixEnd_2406304 := by exact prefixLift 2406304
  have htrace : WordTrace (prefixWord ++ tailWord_2406304) baseStart_2406304 baseEnd_2406304 := by
    simpa [prefixWord, tailWord_2406304, baseEnd_2406304] using wordTrace_append hprefix tailTrace_2406304
  have hstable : (prefixWord ++ tailWord_2406304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406304).length < 2 ^ (prefixWord ++ tailWord_2406304).sum := by decide
  have hdescent : baseEnd_2406304 < baseStart_2406304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406328 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_2406328 : Nat := 118140960795 + 2406328 * 2 ^ 59
def prefixEnd_2406328 : Nat := 4983230072969 + 3 ^ 40 * 2406328 * 2
def baseEnd_2406328 : Nat := 1235602876372366464333505

theorem tailTrace_2406328 : CollatzResearch.WordTrace tailWord_2406328 prefixEnd_2406328 1235602876372366464333505 := by
  unfold tailWord_2406328
  simp only [CollatzResearch.WordTrace]
  refine ⟨43882996213146049474333819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58510661617528065965778425 43882996213146049474333819)
  ·
    refine ⟨65824494319719074211500729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43882996213146049474333819 65824494319719074211500729)
    ·
      refine ⟨49368370739789305658625547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65824494319719074211500729 49368370739789305658625547)
      ·
        refine ⟨74052556109683958487938321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49368370739789305658625547 74052556109683958487938321)
        ·
          refine ⟨55539417082262968865953741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74052556109683958487938321 55539417082262968865953741)
          ·
            refine ⟨20827281405848613324732653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55539417082262968865953741 20827281405848613324732653)
            ·
              refine ⟨7810230527193229996774745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20827281405848613324732653 7810230527193229996774745)
              ·
                refine ⟨5857672895394922497581059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7810230527193229996774745 5857672895394922497581059)
                ·
                  refine ⟨8786509343092383746371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857672895394922497581059 8786509343092383746371589)
                  ·
                    refine ⟨1647470501829821952444673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8786509343092383746371589 1647470501829821952444673)
                    ·
                      refine ⟨1235602876372366464333505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647470501829821952444673 1235602876372366464333505)
                      ·
                        rfl

theorem cell23_2406328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_2406328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406328 prefixEnd_2406328 := by exact prefixLift 2406328
  have htrace : WordTrace (prefixWord ++ tailWord_2406328) baseStart_2406328 baseEnd_2406328 := by
    simpa [prefixWord, tailWord_2406328, baseEnd_2406328] using wordTrace_append hprefix tailTrace_2406328
  have hstable : (prefixWord ++ tailWord_2406328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406328).length < 2 ^ (prefixWord ++ tailWord_2406328).sum := by decide
  have hdescent : baseEnd_2406328 < baseStart_2406328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406385 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 5]
def baseStart_2406385 : Nat := 118140960795 + 2406385 * 2 ^ 59
def prefixEnd_2406385 : Nat := 4983230072969 + 3 ^ 40 * 2406385 * 2
def baseEnd_2406385 : Nat := 137292460529963637924527

theorem tailTrace_2406385 : CollatzResearch.WordTrace tailWord_2406385 prefixEnd_2406385 137292460529963637924527 := by
  unfold tailWord_2406385
  simp only [CollatzResearch.WordTrace]
  refine ⟨87768071387085597683492609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58512047591390398455661739 87768071387085597683492609)
  ·
    refine ⟨65826053540314198262619457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87768071387085597683492609 65826053540314198262619457)
    ·
      refine ⟨49369540155235648696964593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65826053540314198262619457 49369540155235648696964593)
      ·
        refine ⟨37027155116426736522723445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49369540155235648696964593 37027155116426736522723445)
        ·
          refine ⟨3471295792165006549005323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37027155116426736522723445 3471295792165006549005323)
          ·
            refine ⟨5206943688247509823507985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471295792165006549005323 5206943688247509823507985)
            ·
              refine ⟨3905207766185632367630989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5206943688247509823507985 3905207766185632367630989)
              ·
                refine ⟨1464452912319612137861621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3905207766185632367630989 1464452912319612137861621)
                ·
                  refine ⟨137292460529963637924527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464452912319612137861621 137292460529963637924527)
                  ·
                    rfl

theorem cell23_2406385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 5].length) (baseStart_2406385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406385 prefixEnd_2406385 := by exact prefixLift 2406385
  have htrace : WordTrace (prefixWord ++ tailWord_2406385) baseStart_2406385 baseEnd_2406385 := by
    simpa [prefixWord, tailWord_2406385, baseEnd_2406385] using wordTrace_append hprefix tailTrace_2406385
  have hstable : (prefixWord ++ tailWord_2406385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406385).length < 2 ^ (prefixWord ++ tailWord_2406385).sum := by decide
  have hdescent : baseEnd_2406385 < baseStart_2406385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406413 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2406413 : Nat := 118140960795 + 2406413 * 2 ^ 59
def prefixEnd_2406413 : Nat := 4983230072969 + 3 ^ 40 * 2406413 * 2
def baseEnd_2406413 : Nat := 1235646522227998631770615

theorem tailTrace_2406413 : CollatzResearch.WordTrace tailWord_2406413 prefixEnd_2406413 1235646522227998631770615 := by
  unfold tailWord_2406413
  simp only [CollatzResearch.WordTrace]
  refine ⟨87769092630984158465511893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58512728420656105643674595 87769092630984158465511893)
  ·
    refine ⟨2057088108538691214035435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 87769092630984158465511893 2057088108538691214035435)
    ·
      refine ⟨3085632162808036821053153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2057088108538691214035435 3085632162808036821053153)
      ·
        refine ⟨2314224122106027615789865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085632162808036821053153 2314224122106027615789865)
        ·
          refine ⟨1735668091579520711842399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2314224122106027615789865 1735668091579520711842399)
          ·
            refine ⟨2603502137369281067763599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735668091579520711842399 2603502137369281067763599)
            ·
              refine ⟨3905253206053921601645399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603502137369281067763599 3905253206053921601645399)
              ·
                refine ⟨5857879809080882402468099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905253206053921601645399 5857879809080882402468099)
                ·
                  refine ⟨8786819713621323603702149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857879809080882402468099 8786819713621323603702149)
                  ·
                    refine ⟨1647528696303998175694153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8786819713621323603702149 1647528696303998175694153)
                    ·
                      refine ⟨1235646522227998631770615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647528696303998175694153 1235646522227998631770615)
                      ·
                        rfl

theorem cell23_2406413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2406413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406413 prefixEnd_2406413 := by exact prefixLift 2406413
  have htrace : WordTrace (prefixWord ++ tailWord_2406413) baseStart_2406413 baseEnd_2406413 := by
    simpa [prefixWord, tailWord_2406413, baseEnd_2406413] using wordTrace_append hprefix tailTrace_2406413
  have hstable : (prefixWord ++ tailWord_2406413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406413).length < 2 ^ (prefixWord ++ tailWord_2406413).sum := by decide
  have hdescent : baseEnd_2406413 < baseStart_2406413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406431 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2406431 : Nat := 118140960795 + 2406431 * 2 ^ 59
def prefixEnd_2406431 : Nat := 4983230072969 + 3 ^ 40 * 2406431 * 2
def baseEnd_2406431 : Nat := 1235655764879779561345531

theorem tailTrace_2406431 : CollatzResearch.WordTrace tailWord_2406431 prefixEnd_2406431 1235655764879779561345531 := by
  unfold tailWord_2406431
  simp only [CollatzResearch.WordTrace]
  refine ⟨87769749144918947539667147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58513166096612631693111431 87769749144918947539667147)
  ·
    refine ⟨131654623717378421309500721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87769749144918947539667147 131654623717378421309500721)
    ·
      refine ⟨98740967788033815982125541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131654623717378421309500721 98740967788033815982125541)
      ·
        refine ⟨18513931460256340496648539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98740967788033815982125541 18513931460256340496648539)
        ·
          refine ⟨27770897190384510744972809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18513931460256340496648539 27770897190384510744972809)
          ·
            refine ⟨20828172892788383058729607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27770897190384510744972809 20828172892788383058729607)
            ·
              refine ⟨31242259339182574588094411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20828172892788383058729607 31242259339182574588094411)
              ·
                refine ⟨46863389008773861882141617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31242259339182574588094411 46863389008773861882141617)
                ·
                  refine ⟨35147541756580396411606213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46863389008773861882141617 35147541756580396411606213)
                  ·
                    refine ⟨6590164079358824327176165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35147541756580396411606213 6590164079358824327176165)
                    ·
                      refine ⟨1235655764879779561345531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6590164079358824327176165 1235655764879779561345531)
                      ·
                        rfl

theorem cell23_2406431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2406431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406431 prefixEnd_2406431 := by exact prefixLift 2406431
  have htrace : WordTrace (prefixWord ++ tailWord_2406431) baseStart_2406431 baseEnd_2406431 := by
    simpa [prefixWord, tailWord_2406431, baseEnd_2406431] using wordTrace_append hprefix tailTrace_2406431
  have hstable : (prefixWord ++ tailWord_2406431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406431).length < 2 ^ (prefixWord ++ tailWord_2406431).sum := by decide
  have hdescent : baseEnd_2406431 < baseStart_2406431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406452 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2406452 : Nat := 118140960795 + 2406452 * 2 ^ 59
def prefixEnd_2406452 : Nat := 4983230072969 + 3 ^ 40 * 2406452 * 2
def baseEnd_2406452 : Nat := 1235666547973523979182935

theorem tailTrace_2406452 : CollatzResearch.WordTrace tailWord_2406452 prefixEnd_2406452 1235666547973523979182935 := by
  unfold tailWord_2406452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885257538921434063090805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58513676718561912084121073 43885257538921434063090805)
  ·
    refine ⟨4114242894273884443414763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43885257538921434063090805 4114242894273884443414763)
    ·
      refine ⟨6171364341410826665122145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4114242894273884443414763 6171364341410826665122145)
      ·
        refine ⟨4628523256058119998841609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6171364341410826665122145 4628523256058119998841609)
        ·
          refine ⟨3471392442043589999131207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4628523256058119998841609 3471392442043589999131207)
          ·
            refine ⟨5207088663065384998696811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471392442043589999131207 5207088663065384998696811)
            ·
              refine ⟨7810632994598077498045217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207088663065384998696811 7810632994598077498045217)
              ·
                refine ⟨5857974745948558123533913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7810632994598077498045217 5857974745948558123533913)
                ·
                  refine ⟨4393481059461418592650435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857974745948558123533913 4393481059461418592650435)
                  ·
                    refine ⟨6590221589192127888975653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393481059461418592650435 6590221589192127888975653)
                    ·
                      refine ⟨1235666547973523979182935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6590221589192127888975653 1235666547973523979182935)
                      ·
                        rfl

theorem cell23_2406452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2406452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406452 prefixEnd_2406452 := by exact prefixLift 2406452
  have htrace : WordTrace (prefixWord ++ tailWord_2406452) baseStart_2406452 baseEnd_2406452 := by
    simpa [prefixWord, tailWord_2406452, baseEnd_2406452] using wordTrace_append hprefix tailTrace_2406452
  have hstable : (prefixWord ++ tailWord_2406452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406452).length < 2 ^ (prefixWord ++ tailWord_2406452).sum := by decide
  have hdescent : baseEnd_2406452 < baseStart_2406452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406488 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_2406488 : Nat := 118140960795 + 2406488 * 2 ^ 59
def prefixEnd_2406488 : Nat := 4983230072969 + 3 ^ 40 * 2406488 * 2
def baseEnd_2406488 : Nat := 411895011092361946110923

theorem tailTrace_2406488 : CollatzResearch.WordTrace tailWord_2406488 prefixEnd_2406488 411895011092361946110923 := by
  unfold tailWord_2406488
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885914052856223137246059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58514552070474964182994745 43885914052856223137246059)
  ·
    refine ⟨65828871079284334705869089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43885914052856223137246059 65828871079284334705869089)
    ·
      refine ⟨49371653309463251029401817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65828871079284334705869089 49371653309463251029401817)
      ·
        refine ⟨37028739982097438272051363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49371653309463251029401817 37028739982097438272051363)
        ·
          refine ⟨55543109973146157408077045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37028739982097438272051363 55543109973146157408077045)
          ·
            refine ⟨5207166559982452257007223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55543109973146157408077045 5207166559982452257007223)
            ·
              refine ⟨7810749839973678385510835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207166559982452257007223 7810749839973678385510835)
              ·
                refine ⟨11716124759960517578266253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7810749839973678385510835 11716124759960517578266253)
                ·
                  refine ⟨4393546784985194091849845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11716124759960517578266253 4393546784985194091849845)
                  ·
                    refine ⟨411895011092361946110923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4393546784985194091849845 411895011092361946110923)
                    ·
                      rfl

theorem cell23_2406488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_2406488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406488 prefixEnd_2406488 := by exact prefixLift 2406488
  have htrace : WordTrace (prefixWord ++ tailWord_2406488) baseStart_2406488 baseEnd_2406488 := by
    simpa [prefixWord, tailWord_2406488, baseEnd_2406488] using wordTrace_append hprefix tailTrace_2406488
  have hstable : (prefixWord ++ tailWord_2406488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406488).length < 2 ^ (prefixWord ++ tailWord_2406488).sum := by decide
  have hdescent : baseEnd_2406488 < baseStart_2406488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406505 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 1, 5]
def baseStart_2406505 : Nat := 118140960795 + 2406505 * 2 ^ 59
def prefixEnd_2406505 : Nat := 4983230072969 + 3 ^ 40 * 2406505 * 2
def baseEnd_2406505 : Nat := 411897920816070757273397

theorem tailTrace_2406505 : CollatzResearch.WordTrace tailWord_2406505 prefixEnd_2406505 411897920816070757273397 := by
  unfold tailWord_2406505
  simp only [CollatzResearch.WordTrace]
  refine ⟨87772448146650858177860969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58514965431100572118573979 87772448146650858177860969)
  ·
    refine ⟨65829336109988143633395727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87772448146650858177860969 65829336109988143633395727)
    ·
      refine ⟨98744004164982215450093591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65829336109988143633395727 98744004164982215450093591)
      ·
        refine ⟨148116006247473323175140387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98744004164982215450093591 148116006247473323175140387)
        ·
          refine ⟨222174009371209984762710581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148116006247473323175140387 222174009371209984762710581)
          ·
            refine ⟨20828813378550936071504117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222174009371209984762710581 20828813378550936071504117)
            ·
              refine ⟨1952701254239150256703511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20828813378550936071504117 1952701254239150256703511)
              ·
                refine ⟨2929051881358725385055267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952701254239150256703511 2929051881358725385055267)
                ·
                  refine ⟨4393577822038088077582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929051881358725385055267 4393577822038088077582901)
                  ·
                    refine ⟨411897920816070757273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4393577822038088077582901 411897920816070757273397)
                    ·
                      rfl

theorem cell23_2406505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_2406505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406505 prefixEnd_2406505 := by exact prefixLift 2406505
  have htrace : WordTrace (prefixWord ++ tailWord_2406505) baseStart_2406505 baseEnd_2406505 := by
    simpa [prefixWord, tailWord_2406505, baseEnd_2406505] using wordTrace_append hprefix tailTrace_2406505
  have hstable : (prefixWord ++ tailWord_2406505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406505).length < 2 ^ (prefixWord ++ tailWord_2406505).sum := by decide
  have hdescent : baseEnd_2406505 < baseStart_2406505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406519 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 1, 1, 3]
def baseStart_2406519 : Nat := 118140960795 + 2406519 * 2 ^ 59
def prefixEnd_2406519 : Nat := 4983230072969 + 3 ^ 40 * 2406519 * 2
def baseEnd_2406519 : Nat := 1235700951177375217045127

theorem tailTrace_2406519 : CollatzResearch.WordTrace tailWord_2406519 prefixEnd_2406519 1235700951177375217045127 := by
  unfold tailWord_2406519
  simp only [CollatzResearch.WordTrace]
  refine ⟨87772958768600138568870611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58515305845733425712580407 87772958768600138568870611)
  ·
    refine ⟨131659438152900207853305917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87772958768600138568870611 131659438152900207853305917)
    ·
      refine ⟨49372289307337577944989719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131659438152900207853305917 49372289307337577944989719)
      ·
        refine ⟨74058433961006366917484579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49372289307337577944989719 74058433961006366917484579)
        ·
          refine ⟨111087650941509550376226869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74058433961006366917484579 111087650941509550376226869)
          ·
            refine ⟨10414467275766520347771269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111087650941509550376226869 10414467275766520347771269)
            ·
              refine ⟨1952712614206222565207113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10414467275766520347771269 1952712614206222565207113)
              ·
                refine ⟨1464534460654666923905335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952712614206222565207113 1464534460654666923905335)
                ·
                  refine ⟨2196801690982000385858003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464534460654666923905335 2196801690982000385858003)
                  ·
                    refine ⟨3295202536473000578787005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2196801690982000385858003 3295202536473000578787005)
                    ·
                      refine ⟨1235700951177375217045127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295202536473000578787005 1235700951177375217045127)
                      ·
                        rfl

theorem cell23_2406519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_2406519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406519 prefixEnd_2406519 := by exact prefixLift 2406519
  have htrace : WordTrace (prefixWord ++ tailWord_2406519) baseStart_2406519 baseEnd_2406519 := by
    simpa [prefixWord, tailWord_2406519, baseEnd_2406519] using wordTrace_append hprefix tailTrace_2406519
  have hstable : (prefixWord ++ tailWord_2406519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406519).length < 2 ^ (prefixWord ++ tailWord_2406519).sum := by decide
  have hdescent : baseEnd_2406519 < baseStart_2406519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406535 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 2, 4]
def baseStart_2406535 : Nat := 118140960795 + 2406535 * 2 ^ 59
def prefixEnd_2406535 : Nat := 4983230072969 + 3 ^ 40 * 2406535 * 2
def baseEnd_2406535 : Nat := 411903055622615718148351

theorem tailTrace_2406535 : CollatzResearch.WordTrace tailWord_2406535 prefixEnd_2406535 411903055622615718148351 := by
  unfold tailWord_2406535
  simp only [CollatzResearch.WordTrace]
  refine ⟨87773542336542173301453059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58515694891028115534302039 87773542336542173301453059)
  ·
    refine ⟨131660313504813259952179589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87773542336542173301453059 131660313504813259952179589)
    ·
      refine ⟨24686308782152486241033673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131660313504813259952179589 24686308782152486241033673)
      ·
        refine ⟨18514731586614364680775255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24686308782152486241033673 18514731586614364680775255)
        ·
          refine ⟨27772097379921547021162883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18514731586614364680775255 27772097379921547021162883)
          ·
            refine ⟨41658146069882320531744325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27772097379921547021162883 41658146069882320531744325)
            ·
              refine ⟨7810902388102935099702061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41658146069882320531744325 7810902388102935099702061)
              ·
                refine ⟨2929088395538600662388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7810902388102935099702061 2929088395538600662388273)
                ·
                  refine ⟨2196816296653950496791205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929088395538600662388273 2196816296653950496791205)
                  ·
                    refine ⟨411903055622615718148351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2196816296653950496791205 411903055622615718148351)
                    ·
                      rfl

theorem cell23_2406535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_2406535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406535 prefixEnd_2406535 := by exact prefixLift 2406535
  have htrace : WordTrace (prefixWord ++ tailWord_2406535) baseStart_2406535 baseEnd_2406535 := by
    simpa [prefixWord, tailWord_2406535, baseEnd_2406535] using wordTrace_append hprefix tailTrace_2406535
  have hstable : (prefixWord ++ tailWord_2406535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406535).length < 2 ^ (prefixWord ++ tailWord_2406535).sum := by decide
  have hdescent : baseEnd_2406535 < baseStart_2406535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406559 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2406559 : Nat := 118140960795 + 2406559 * 2 ^ 59
def prefixEnd_2406559 : Nat := 4983230072969 + 3 ^ 40 * 2406559 * 2
def baseEnd_2406559 : Nat := 1235721490403555060544943

theorem tailTrace_2406559 : CollatzResearch.WordTrace tailWord_2406559 prefixEnd_2406559 1235721490403555060544943 := by
  unfold tailWord_2406559
  simp only [CollatzResearch.WordTrace]
  refine ⟨87774417688455225400326731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58516278458970150266884487 87774417688455225400326731)
  ·
    refine ⟨131661626532682838100490097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87774417688455225400326731 131661626532682838100490097)
    ·
      refine ⟨98746219899512128575367573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131661626532682838100490097 98746219899512128575367573)
      ·
        refine ⟨4628729057789631026970355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98746219899512128575367573 4628729057789631026970355)
        ·
          refine ⟨6943093586684446540455533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628729057789631026970355 6943093586684446540455533)
          ·
            refine ⟨2603660095006667452670825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6943093586684446540455533 2603660095006667452670825)
            ·
              refine ⟨1952745071255000589503119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603660095006667452670825 1952745071255000589503119)
              ·
                refine ⟨2929117606882500884254679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952745071255000589503119 2929117606882500884254679)
                ·
                  refine ⟨4393676410323751326382019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929117606882500884254679 4393676410323751326382019)
                  ·
                    refine ⟨6590514615485626989573029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393676410323751326382019 6590514615485626989573029)
                    ·
                      refine ⟨1235721490403555060544943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6590514615485626989573029 1235721490403555060544943)
                      ·
                        rfl

theorem cell23_2406559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2406559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406559 prefixEnd_2406559 := by exact prefixLift 2406559
  have htrace : WordTrace (prefixWord ++ tailWord_2406559) baseStart_2406559 baseEnd_2406559 := by
    simpa [prefixWord, tailWord_2406559, baseEnd_2406559] using wordTrace_append hprefix tailTrace_2406559
  have hstable : (prefixWord ++ tailWord_2406559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406559).length < 2 ^ (prefixWord ++ tailWord_2406559).sum := by decide
  have hdescent : baseEnd_2406559 < baseStart_2406559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406592 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_2406592 : Nat := 118140960795 + 2406592 * 2 ^ 59
def prefixEnd_2406592 : Nat := 4983230072969 + 3 ^ 40 * 2406592 * 2
def baseEnd_2406592 : Nat := 1235738435265153431432291

theorem tailTrace_2406592 : CollatzResearch.WordTrace tailWord_2406592 prefixEnd_2406592 1235738435265153431432291 := by
  unfold tailWord_2406592
  simp only [CollatzResearch.WordTrace]
  refine ⟨43887810648667836018139015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58517080864890448024185353 43887810648667836018139015)
  ·
    refine ⟨65831715973001754027208523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43887810648667836018139015 65831715973001754027208523)
    ·
      refine ⟨98747573959502631040812785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65831715973001754027208523 98747573959502631040812785)
      ·
        refine ⟨74060680469626973280609589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98747573959502631040812785 74060680469626973280609589)
        ·
          refine ⟨6943188794027528745057149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74060680469626973280609589 6943188794027528745057149)
          ·
            refine ⟨2603695797760323279396431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6943188794027528745057149 2603695797760323279396431)
            ·
              refine ⟨3905543696640484919094647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603695797760323279396431 3905543696640484919094647)
              ·
                refine ⟨5858315544960727378641971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905543696640484919094647 5858315544960727378641971)
                ·
                  refine ⟨8787473317441091067962957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5858315544960727378641971 8787473317441091067962957)
                  ·
                    refine ⟨3295302494040409150486109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8787473317441091067962957 3295302494040409150486109)
                    ·
                      refine ⟨1235738435265153431432291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295302494040409150486109 1235738435265153431432291)
                      ·
                        rfl

theorem cell23_2406592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_2406592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406592 prefixEnd_2406592 := by exact prefixLift 2406592
  have htrace : WordTrace (prefixWord ++ tailWord_2406592) baseStart_2406592 baseEnd_2406592 := by
    simpa [prefixWord, tailWord_2406592, baseEnd_2406592] using wordTrace_append hprefix tailTrace_2406592
  have hstable : (prefixWord ++ tailWord_2406592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406592).length < 2 ^ (prefixWord ++ tailWord_2406592).sum := by decide
  have hdescent : baseEnd_2406592 < baseStart_2406592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406615 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_2406615 : Nat := 118140960795 + 2406615 * 2 ^ 59
def prefixEnd_2406615 : Nat := 4983230072969 + 3 ^ 40 * 2406615 * 2
def baseEnd_2406615 : Nat := 1235750245320206841444685

theorem tailTrace_2406615 : CollatzResearch.WordTrace tailWord_2406615 prefixEnd_2406615 1235750245320206841444685 := by
  unfold tailWord_2406615
  simp only [CollatzResearch.WordTrace]
  refine ⟨87776460176252346964365299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58517640117501564642910199 87776460176252346964365299)
  ·
    refine ⟨131664690264378520446547949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87776460176252346964365299 131664690264378520446547949)
    ·
      refine ⟨49374258849141945167455481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131664690264378520446547949 49374258849141945167455481)
      ·
        refine ⟨37030694136856458875591611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49374258849141945167455481 37030694136856458875591611)
        ·
          refine ⟨55546041205284688313387417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37030694136856458875591611 55546041205284688313387417)
          ·
            refine ⟨41659530903963516235040563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55546041205284688313387417 41659530903963516235040563)
            ·
              refine ⟨62489296355945274352560845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41659530903963516235040563 62489296355945274352560845)
              ·
                refine ⟨23433486133479477882210317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62489296355945274352560845 23433486133479477882210317)
                ·
                  refine ⟨8787557300054804205828869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23433486133479477882210317 8787557300054804205828869)
                  ·
                    refine ⟨1647666993760275788592913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8787557300054804205828869 1647666993760275788592913)
                    ·
                      refine ⟨1235750245320206841444685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647666993760275788592913 1235750245320206841444685)
                      ·
                        rfl

theorem cell23_2406615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_2406615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406615 prefixEnd_2406615 := by exact prefixLift 2406615
  have htrace : WordTrace (prefixWord ++ tailWord_2406615) baseStart_2406615 baseEnd_2406615 := by
    simpa [prefixWord, tailWord_2406615, baseEnd_2406615] using wordTrace_append hprefix tailTrace_2406615
  have hstable : (prefixWord ++ tailWord_2406615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406615).length < 2 ^ (prefixWord ++ tailWord_2406615).sum := by decide
  have hdescent : baseEnd_2406615 < baseStart_2406615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406618 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2406618 : Nat := 118140960795 + 2406618 * 2 ^ 59
def prefixEnd_2406618 : Nat := 4983230072969 + 3 ^ 40 * 2406618 * 2
def baseEnd_2406618 : Nat := 1235751785762170329707171

theorem tailTrace_2406618 : CollatzResearch.WordTrace tailWord_2406618 prefixEnd_2406618 1235751785762170329707171 := by
  unfold tailWord_2406618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944142398810369619181127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58517713063494318984483005 21944142398810369619181127)
  ·
    refine ⟨32916213598215554428771691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21944142398810369619181127 32916213598215554428771691)
    ·
      refine ⟨49374320397323331643157537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32916213598215554428771691 49374320397323331643157537)
      ·
        refine ⟨37030740297992498732368153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49374320397323331643157537 37030740297992498732368153)
        ·
          refine ⟨27773055223494374049276115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37030740297992498732368153 27773055223494374049276115)
          ·
            refine ⟨41659582835241561073914173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27773055223494374049276115 41659582835241561073914173)
            ·
              refine ⟨15622343563215585402717815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41659582835241561073914173 15622343563215585402717815)
              ·
                refine ⟨23433515344823378104076723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15622343563215585402717815 23433515344823378104076723)
                ·
                  refine ⟨35150273017235067156115085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23433515344823378104076723 35150273017235067156115085)
                  ·
                    refine ⟨13181352381463150183543157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35150273017235067156115085 13181352381463150183543157)
                    ·
                      refine ⟨1235751785762170329707171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13181352381463150183543157 1235751785762170329707171)
                      ·
                        rfl

theorem cell23_2406618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2406618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406618 prefixEnd_2406618 := by exact prefixLift 2406618
  have htrace : WordTrace (prefixWord ++ tailWord_2406618) baseStart_2406618 baseEnd_2406618 := by
    simpa [prefixWord, tailWord_2406618, baseEnd_2406618] using wordTrace_append hprefix tailTrace_2406618
  have hstable : (prefixWord ++ tailWord_2406618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406618).length < 2 ^ (prefixWord ++ tailWord_2406618).sum := by decide
  have hdescent : baseEnd_2406618 < baseStart_2406618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406675 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 5, 2]
def baseStart_2406675 : Nat := 118140960795 + 2406675 * 2 ^ 59
def prefixEnd_2406675 : Nat := 4983230072969 + 3 ^ 40 * 2406675 * 2
def baseEnd_2406675 : Nat := 1235781054159476606694409

theorem tailTrace_2406675 : CollatzResearch.WordTrace tailWord_2406675 prefixEnd_2406675 1235781054159476606694409 := by
  unfold tailWord_2406675
  simp only [CollatzResearch.WordTrace]
  refine ⟨87778648556034977211549479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58519099037356651474366319 87778648556034977211549479)
  ·
    refine ⟨131667972834052465817324219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87778648556034977211549479 131667972834052465817324219)
    ·
      refine ⟨197501959251078698725986329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131667972834052465817324219 197501959251078698725986329)
      ·
        refine ⟨148126469438309024044489747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197501959251078698725986329 148126469438309024044489747)
        ·
          refine ⟨222189704157463536066734621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148126469438309024044489747 222189704157463536066734621)
          ·
            refine ⟨83321139059048826025025483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222189704157463536066734621 83321139059048826025025483)
            ·
              refine ⟨124981708588573239037538225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83321139059048826025025483 124981708588573239037538225)
              ·
                refine ⟨93736281441429929278153669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124981708588573239037538225 93736281441429929278153669)
                ·
                  refine ⟨17575552770268111739653813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93736281441429929278153669 17575552770268111739653813)
                  ·
                    refine ⟨1647708072212635475592545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17575552770268111739653813 1647708072212635475592545)
                    ·
                      refine ⟨1235781054159476606694409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647708072212635475592545 1235781054159476606694409)
                      ·
                        rfl

theorem cell23_2406675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 5, 2].length) (baseStart_2406675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406675 prefixEnd_2406675 := by exact prefixLift 2406675
  have htrace : WordTrace (prefixWord ++ tailWord_2406675) baseStart_2406675 baseEnd_2406675 := by
    simpa [prefixWord, tailWord_2406675, baseEnd_2406675] using wordTrace_append hprefix tailTrace_2406675
  have hstable : (prefixWord ++ tailWord_2406675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406675).length < 2 ^ (prefixWord ++ tailWord_2406675).sum := by decide
  have hdescent : baseEnd_2406675 < baseStart_2406675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406692 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_2406692 : Nat := 118140960795 + 2406692 * 2 ^ 59
def prefixEnd_2406692 : Nat := 4983230072969 + 3 ^ 40 * 2406692 * 2
def baseEnd_2406692 : Nat := 1235789783330603040181831

theorem tailTrace_2406692 : CollatzResearch.WordTrace tailWord_2406692 prefixEnd_2406692 1235789783330603040181831 := by
  unfold tailWord_2406692
  simp only [CollatzResearch.WordTrace]
  refine ⟨43889634298486694557459165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58519512397982259409945553 43889634298486694557459165)
  ·
    refine ⟨16458612861932510459047187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43889634298486694557459165 16458612861932510459047187)
    ·
      refine ⟨24687919292898765688570781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16458612861932510459047187 24687919292898765688570781)
      ·
        refine ⟨9257969734837037133214043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24687919292898765688570781 9257969734837037133214043)
        ·
          refine ⟨13886954602255555699821065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9257969734837037133214043 13886954602255555699821065)
          ·
            refine ⟨10415215951691666774865799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13886954602255555699821065 10415215951691666774865799)
            ·
              refine ⟨15622823927537500162298699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10415215951691666774865799 15622823927537500162298699)
              ·
                refine ⟨23434235891306250243448049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15622823927537500162298699 23434235891306250243448049)
                ·
                  refine ⟨17575676918479687682586037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23434235891306250243448049 17575676918479687682586037)
                  ·
                    refine ⟨1647719711107470720242441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17575676918479687682586037 1647719711107470720242441)
                    ·
                      refine ⟨1235789783330603040181831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647719711107470720242441 1235789783330603040181831)
                      ·
                        rfl

theorem cell23_2406692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_2406692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406692 prefixEnd_2406692 := by exact prefixLift 2406692
  have htrace : WordTrace (prefixWord ++ tailWord_2406692) baseStart_2406692 baseEnd_2406692 := by
    simpa [prefixWord, tailWord_2406692, baseEnd_2406692] using wordTrace_append hprefix tailTrace_2406692
  have hstable : (prefixWord ++ tailWord_2406692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406692).length < 2 ^ (prefixWord ++ tailWord_2406692).sum := by decide
  have hdescent : baseEnd_2406692 < baseStart_2406692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
